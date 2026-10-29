import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part259Data0
import BstLean.Part259Data1
import BstLean.Part259Data2
import BstLean.Part259Data3
import BstLean.Part259Data4
import BstLean.Part260First
#eval (do IO.println s!"P260 START 12225 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12225
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12225 = 202009148155087 := by
  have hu : mW 12225 ≤ 202009148155087 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12225 ≤ 202009148155086 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12225)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24450 ^ 2)
    ((1000000000000000000/153623880760540889361183))
    ((25000000000000000000/3840439939380842744355427)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24450) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24450 : ℝ)^2 / (mW 12225 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1058357/500000000000))/2) * ((1-firstRatio 24450) * √(1-firstRatio 24450) *
      sixthConstant (e1CovarianceRatio 24450 (mW 12225) (1/10^6) rowEps))) /
    (712/10000 - 24450*(1+1/10^6)*((1058357/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24450 (mW 12225) /
    ((1/10^5) * ((mW 12225 : ℝ)*24450*((mW 12225 : ℝ)+24450+1)))^2 +
  8*(mW 12225 : ℝ)*24450*(24450+2)*(24450+3) /
    ((1/1000)*((mW 12225 : ℝ)*24450*(24450+2)))^2 +
  covarianceVarianceBound 24450 (mW 12225) /
    ((1/1000)*covarianceMeanBound 24450 (mW 12225))^2 +
  normVarianceBound 24450 (mW 12225) / (3*inputVarianceMean 24450 (mW 12225))^2

end BstLean.Part260.Row12225
#eval (do IO.println s!"P260 END 12225 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12227 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12227
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12227 = 202124841671274 := by
  have hu : mW 12227 ≤ 202124841671274 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12227 ≤ 202124841671273 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12227)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24454 ^ 2)
    ((25000000000000000000/3841225337544240192677269))
    ((25000000000000000000/3841068257911560703003119)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24454) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24454 : ℝ)^2 / (mW 12227 : ℝ)) * (1 + 1/10^6)^2 *
    √(((529091/250000000000))/2) * ((1-firstRatio 24454) * √(1-firstRatio 24454) *
      sixthConstant (e1CovarianceRatio 24454 (mW 12227) (1/10^6) rowEps))) /
    (712/10000 - 24454*(1+1/10^6)*((529091/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24454 (mW 12227) /
    ((1/10^5) * ((mW 12227 : ℝ)*24454*((mW 12227 : ℝ)+24454+1)))^2 +
  8*(mW 12227 : ℝ)*24454*(24454+2)*(24454+3) /
    ((1/1000)*((mW 12227 : ℝ)*24454*(24454+2)))^2 +
  covarianceVarianceBound 24454 (mW 12227) /
    ((1/1000)*covarianceMeanBound 24454 (mW 12227))^2 +
  normVarianceBound 24454 (mW 12227) / (3*inputVarianceMean 24454 (mW 12227))^2

end BstLean.Part260.Row12227
#eval (do IO.println s!"P260 END 12227 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12228 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12228
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12228 = 202182706173772 := by
  have hu : mW 12228 ≤ 202182706173772 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12228 ≤ 202182706173771 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12228)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24456 ^ 2)
    ((6250000000000000000/960384874202399793000279))
    ((5000000000000000000/768276483435383936465393)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24456) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24456 : ℝ)^2 / (mW 12228 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2116189/1000000000000))/2) * ((1-firstRatio 24456) * √(1-firstRatio 24456) *
      sixthConstant (e1CovarianceRatio 24456 (mW 12228) (1/10^6) rowEps))) /
    (712/10000 - 24456*(1+1/10^6)*((2116189/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24456 (mW 12228) /
    ((1/10^5) * ((mW 12228 : ℝ)*24456*((mW 12228 : ℝ)+24456+1)))^2 +
  8*(mW 12228 : ℝ)*24456*(24456+2)*(24456+3) /
    ((1/1000)*((mW 12228 : ℝ)*24456*(24456+2)))^2 +
  covarianceVarianceBound 24456 (mW 12228) /
    ((1/1000)*covarianceMeanBound 24456 (mW 12228))^2 +
  normVarianceBound 24456 (mW 12228) / (3*inputVarianceMean 24456 (mW 12228))^2

end BstLean.Part260.Row12228
#eval (do IO.println s!"P260 END 12228 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12229 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12229
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12229 = 202240582507808 := by
  have hu : mW 12229 ≤ 202240582507808 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12229 ≤ 202240582507807 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12229)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24458 ^ 2)
    ((25000000000000000000/3841853656074958151324963))
    ((25000000000000000000/3841696576442278661650811)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24458) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24458 : ℝ)^2 / (mW 12229 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1058007/500000000000))/2) * ((1-firstRatio 24458) * √(1-firstRatio 24458) *
      sixthConstant (e1CovarianceRatio 24458 (mW 12229) (1/10^6) rowEps))) /
    (712/10000 - 24458*(1+1/10^6)*((1058007/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24458 (mW 12229) /
    ((1/10^5) * ((mW 12229 : ℝ)*24458*((mW 12229 : ℝ)+24458+1)))^2 +
  8*(mW 12229 : ℝ)*24458*(24458+2)*(24458+3) /
    ((1/1000)*((mW 12229 : ℝ)*24458*(24458+2)))^2 +
  covarianceVarianceBound 24458 (mW 12229) /
    ((1/1000)*covarianceMeanBound 24458 (mW 12229))^2 +
  normVarianceBound 24458 (mW 12229) / (3*inputVarianceMean 24458 (mW 12229))^2

end BstLean.Part260.Row12229
#eval (do IO.println s!"P260 END 12229 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12230 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12230
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12230 = 202298470674833 := by
  have hu : mW 12230 ≤ 202298470674833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12230 ≤ 202298470674832 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12230)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24460 ^ 2)
    ((2500000000000000000/384216781534031713064881))
    ((25000000000000000000/3842010735707637640974657)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24460) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24460 : ℝ)^2 / (mW 12230 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2115839/1000000000000))/2) * ((1-firstRatio 24460) * √(1-firstRatio 24460) *
      sixthConstant (e1CovarianceRatio 24460 (mW 12230) (1/10^6) rowEps))) /
    (712/10000 - 24460*(1+1/10^6)*((2115839/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24460 (mW 12230) /
    ((1/10^5) * ((mW 12230 : ℝ)*24460*((mW 12230 : ℝ)+24460+1)))^2 +
  8*(mW 12230 : ℝ)*24460*(24460+2)*(24460+3) /
    ((1/1000)*((mW 12230 : ℝ)*24460*(24460+2)))^2 +
  covarianceVarianceBound 24460 (mW 12230) /
    ((1/1000)*covarianceMeanBound 24460 (mW 12230))^2 +
  normVarianceBound 24460 (mW 12230) / (3*inputVarianceMean 24460 (mW 12230))^2

end BstLean.Part260.Row12230
#eval (do IO.println s!"P260 END 12230 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12231 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12231
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12231 = 202356370676299 := by
  have hu : mW 12231 ≤ 202356370676299 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12231 ≤ 202356370676298 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12231)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24462 ^ 2)
    ((25000000000000000000/3842481974605676109972657))
    ((25000000000000000000/3842324894972996620298503)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24462) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24462 : ℝ)^2 / (mW 12231 : ℝ)) * (1 + 1/10^6)^2 *
    √(((423133/200000000000))/2) * ((1-firstRatio 24462) * √(1-firstRatio 24462) *
      sixthConstant (e1CovarianceRatio 24462 (mW 12231) (1/10^6) rowEps))) /
    (712/10000 - 24462*(1+1/10^6)*((423133/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24462 (mW 12231) /
    ((1/10^5) * ((mW 12231 : ℝ)*24462*((mW 12231 : ℝ)+24462+1)))^2 +
  8*(mW 12231 : ℝ)*24462*(24462+2)*(24462+3) /
    ((1/1000)*((mW 12231 : ℝ)*24462*(24462+2)))^2 +
  covarianceVarianceBound 24462 (mW 12231) /
    ((1/1000)*covarianceMeanBound 24462 (mW 12231))^2 +
  normVarianceBound 24462 (mW 12231) / (3*inputVarianceMean 24462 (mW 12231))^2

end BstLean.Part260.Row12231
#eval (do IO.println s!"P260 END 12231 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12232 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12232
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12232 = 202414282513656 := by
  have hu : mW 12232 ≤ 202414282513656 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12232 ≤ 202414282513655 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12232)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24464 ^ 2)
    ((3125000000000000000/480349516733879386162063))
    ((25000000000000000000/3842639054238355599622349)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24464) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24464 : ℝ)^2 / (mW 12232 : ℝ)) * (1 + 1/10^6)^2 *
    √(((211549/100000000000))/2) * ((1-firstRatio 24464) * √(1-firstRatio 24464) *
      sixthConstant (e1CovarianceRatio 24464 (mW 12232) (1/10^6) rowEps))) /
    (712/10000 - 24464*(1+1/10^6)*((211549/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24464 (mW 12232) /
    ((1/10^5) * ((mW 12232 : ℝ)*24464*((mW 12232 : ℝ)+24464+1)))^2 +
  8*(mW 12232 : ℝ)*24464*(24464+2)*(24464+3) /
    ((1/1000)*((mW 12232 : ℝ)*24464*(24464+2)))^2 +
  covarianceVarianceBound 24464 (mW 12232) /
    ((1/1000)*covarianceMeanBound 24464 (mW 12232))^2 +
  normVarianceBound 24464 (mW 12232) / (3*inputVarianceMean 24464 (mW 12232))^2

end BstLean.Part260.Row12232
#eval (do IO.println s!"P260 END 12232 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12233 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12233
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12233 = 202472206188358 := by
  have hu : mW 12233 ≤ 202472206188358 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12233 ≤ 202472206188357 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12233)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24466 ^ 2)
    ((25000000000000000000/3843110293136394068620351))
    ((5000000000000000000/768590642700742915789239)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24466) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24466 : ℝ)^2 / (mW 12233 : ℝ)) * (1 + 1/10^6)^2 *
    √(((423063/200000000000))/2) * ((1-firstRatio 24466) * √(1-firstRatio 24466) *
      sixthConstant (e1CovarianceRatio 24466 (mW 12233) (1/10^6) rowEps))) /
    (712/10000 - 24466*(1+1/10^6)*((423063/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24466 (mW 12233) /
    ((1/10^5) * ((mW 12233 : ℝ)*24466*((mW 12233 : ℝ)+24466+1)))^2 +
  8*(mW 12233 : ℝ)*24466*(24466+2)*(24466+3) /
    ((1/1000)*((mW 12233 : ℝ)*24466*(24466+2)))^2 +
  covarianceVarianceBound 24466 (mW 12233) /
    ((1/1000)*covarianceMeanBound 24466 (mW 12233))^2 +
  normVarianceBound 24466 (mW 12233) / (3*inputVarianceMean 24466 (mW 12233))^2

end BstLean.Part260.Row12233
#eval (do IO.println s!"P260 END 12233 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12234 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12234
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12234 = 202530141701855 := by
  have hu : mW 12234 ≤ 202530141701855 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12234 ≤ 202530141701854 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12234)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24468 ^ 2)
    ((12500000000000000000/1921712226200876523972099))
    ((25000000000000000000/3843267372769073558270041)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24468) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24468 : ℝ)^2 / (mW 12234 : ℝ)) * (1 + 1/10^6)^2 *
    √(((105757/50000000000))/2) * ((1-firstRatio 24468) * √(1-firstRatio 24468) *
      sixthConstant (e1CovarianceRatio 24468 (mW 12234) (1/10^6) rowEps))) /
    (712/10000 - 24468*(1+1/10^6)*((105757/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24468 (mW 12234) /
    ((1/10^5) * ((mW 12234 : ℝ)*24468*((mW 12234 : ℝ)+24468+1)))^2 +
  8*(mW 12234 : ℝ)*24468*(24468+2)*(24468+3) /
    ((1/1000)*((mW 12234 : ℝ)*24468*(24468+2)))^2 +
  covarianceVarianceBound 24468 (mW 12234) /
    ((1/1000)*covarianceMeanBound 24468 (mW 12234))^2 +
  normVarianceBound 24468 (mW 12234) / (3*inputVarianceMean 24468 (mW 12234))^2

end BstLean.Part260.Row12234
#eval (do IO.println s!"P260 END 12234 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12235 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12235
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12235 = 202588089055600 := by
  have hu : mW 12235 ≤ 202588089055600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12235 ≤ 202588089055599 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12235)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24470 ^ 2)
    ((5000000000000000000/768747722333422405453609))
    ((25000000000000000000/3843581532034432537593887)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24470) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24470 : ℝ)^2 / (mW 12235 : ℝ)) * (1 + 1/10^6)^2 *
    √(((422993/200000000000))/2) * ((1-firstRatio 24470) * √(1-firstRatio 24470) *
      sixthConstant (e1CovarianceRatio 24470 (mW 12235) (1/10^6) rowEps))) /
    (712/10000 - 24470*(1+1/10^6)*((422993/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24470 (mW 12235) /
    ((1/10^5) * ((mW 12235 : ℝ)*24470*((mW 12235 : ℝ)+24470+1)))^2 +
  8*(mW 12235 : ℝ)*24470*(24470+2)*(24470+3) /
    ((1/1000)*((mW 12235 : ℝ)*24470*(24470+2)))^2 +
  covarianceVarianceBound 24470 (mW 12235) /
    ((1/1000)*covarianceMeanBound 24470 (mW 12235))^2 +
  normVarianceBound 24470 (mW 12235) / (3*inputVarianceMean 24470 (mW 12235))^2

end BstLean.Part260.Row12235
#eval (do IO.println s!"P260 END 12235 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12236 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12236
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12236 = 202646048251043 := by
  have hu : mW 12236 ≤ 202646048251043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12236 ≤ 202646048251042 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12236)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24472 ^ 2)
    ((6250000000000000000/961013192733117751647973))
    ((25000000000000000000/3843895691299791516917733)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24472) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24472 : ℝ)^2 / (mW 12236 : ℝ)) * (1 + 1/10^6)^2 *
    √(((211479/100000000000))/2) * ((1-firstRatio 24472) * √(1-firstRatio 24472) *
      sixthConstant (e1CovarianceRatio 24472 (mW 12236) (1/10^6) rowEps))) /
    (712/10000 - 24472*(1+1/10^6)*((211479/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24472 (mW 12236) /
    ((1/10^5) * ((mW 12236 : ℝ)*24472*((mW 12236 : ℝ)+24472+1)))^2 +
  8*(mW 12236 : ℝ)*24472*(24472+2)*(24472+3) /
    ((1/1000)*((mW 12236 : ℝ)*24472*(24472+2)))^2 +
  covarianceVarianceBound 24472 (mW 12236) /
    ((1/1000)*covarianceMeanBound 24472 (mW 12236))^2 +
  normVarianceBound 24472 (mW 12236) / (3*inputVarianceMean 24472 (mW 12236))^2

end BstLean.Part260.Row12236
#eval (do IO.println s!"P260 END 12236 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12237 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12237
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12237 = 202704019289637 := by
  have hu : mW 12237 ≤ 202704019289637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12237 ≤ 202704019289636 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12237)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24474 ^ 2)
    ((25000000000000000000/3844366930197829985915739))
    ((25000000000000000000/3844209850565150496241579)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24474) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24474 : ℝ)^2 / (mW 12237 : ℝ)) * (1 + 1/10^6)^2 *
    √(((264327/125000000000))/2) * ((1-firstRatio 24474) * √(1-firstRatio 24474) *
      sixthConstant (e1CovarianceRatio 24474 (mW 12237) (1/10^6) rowEps))) /
    (712/10000 - 24474*(1+1/10^6)*((264327/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24474 (mW 12237) /
    ((1/10^5) * ((mW 12237 : ℝ)*24474*((mW 12237 : ℝ)+24474+1)))^2 +
  8*(mW 12237 : ℝ)*24474*(24474+2)*(24474+3) /
    ((1/1000)*((mW 12237 : ℝ)*24474*(24474+2)))^2 +
  covarianceVarianceBound 24474 (mW 12237) /
    ((1/1000)*covarianceMeanBound 24474 (mW 12237))^2 +
  normVarianceBound 24474 (mW 12237) / (3*inputVarianceMean 24474 (mW 12237))^2

end BstLean.Part260.Row12237
#eval (do IO.println s!"P260 END 12237 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12238 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12238
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12238 = 202762002172833 := by
  have hu : mW 12238 ≤ 202762002172833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12238 ≤ 202762002172832 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12238)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24476 ^ 2)
    ((12500000000000000000/1922340544731594482619793))
    ((1000000000000000000/153780960393220379022617)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24476) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24476 : ℝ)^2 / (mW 12238 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2114441/1000000000000))/2) * ((1-firstRatio 24476) * √(1-firstRatio 24476) *
      sixthConstant (e1CovarianceRatio 24476 (mW 12238) (1/10^6) rowEps))) /
    (712/10000 - 24476*(1+1/10^6)*((2114441/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24476 (mW 12238) /
    ((1/10^5) * ((mW 12238 : ℝ)*24476*((mW 12238 : ℝ)+24476+1)))^2 +
  8*(mW 12238 : ℝ)*24476*(24476+2)*(24476+3) /
    ((1/1000)*((mW 12238 : ℝ)*24476*(24476+2)))^2 +
  covarianceVarianceBound 24476 (mW 12238) /
    ((1/1000)*covarianceMeanBound 24476 (mW 12238))^2 +
  normVarianceBound 24476 (mW 12238) / (3*inputVarianceMean 24476 (mW 12238))^2

end BstLean.Part260.Row12238
#eval (do IO.println s!"P260 END 12238 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12239 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12239
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12239 = 202819996902084 := by
  have hu : mW 12239 ≤ 202819996902084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12239 ≤ 202819996902083 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12239)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24478 ^ 2)
    ((25000000000000000000/3844995248728547944563433))
    ((25000000000000000000/3844838169095868454889271)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24478) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24478 : ℝ)^2 / (mW 12239 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1057133/500000000000))/2) * ((1-firstRatio 24478) * √(1-firstRatio 24478) *
      sixthConstant (e1CovarianceRatio 24478 (mW 12239) (1/10^6) rowEps))) /
    (712/10000 - 24478*(1+1/10^6)*((1057133/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24478 (mW 12239) /
    ((1/10^5) * ((mW 12239 : ℝ)*24478*((mW 12239 : ℝ)+24478+1)))^2 +
  8*(mW 12239 : ℝ)*24478*(24478+2)*(24478+3) /
    ((1/1000)*((mW 12239 : ℝ)*24478*(24478+2)))^2 +
  covarianceVarianceBound 24478 (mW 12239) /
    ((1/1000)*covarianceMeanBound 24478 (mW 12239))^2 +
  normVarianceBound 24478 (mW 12239) / (3*inputVarianceMean 24478 (mW 12239))^2

end BstLean.Part260.Row12239
#eval (do IO.println s!"P260 END 12239 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12240 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12240
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12240 = 202878003478842 := by
  have hu : mW 12240 ≤ 202878003478842 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12240 ≤ 202878003478841 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12240)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24480 ^ 2)
    ((312500000000000000/48066367599923836548591))
    ((25000000000000000000/3845152328361227434213117)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24480) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24480 : ℝ)^2 / (mW 12240 : ℝ)) * (1 + 1/10^6)^2 *
    √(((528523/250000000000))/2) * ((1-firstRatio 24480) * √(1-firstRatio 24480) *
      sixthConstant (e1CovarianceRatio 24480 (mW 12240) (1/10^6) rowEps))) /
    (712/10000 - 24480*(1+1/10^6)*((528523/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24480 (mW 12240) /
    ((1/10^5) * ((mW 12240 : ℝ)*24480*((mW 12240 : ℝ)+24480+1)))^2 +
  8*(mW 12240 : ℝ)*24480*(24480+2)*(24480+3) /
    ((1/1000)*((mW 12240 : ℝ)*24480*(24480+2)))^2 +
  covarianceVarianceBound 24480 (mW 12240) /
    ((1/1000)*covarianceMeanBound 24480 (mW 12240))^2 +
  normVarianceBound 24480 (mW 12240) / (3*inputVarianceMean 24480 (mW 12240))^2

end BstLean.Part260.Row12240
#eval (do IO.println s!"P260 END 12240 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12241 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12241
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12241 = 202936021904558 := by
  have hu : mW 12241 ≤ 202936021904558 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12241 ≤ 202936021904557 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12241)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24482 ^ 2)
    ((25000000000000000000/3845623567259265903211127))
    ((25000000000000000000/3845466487626586413536963)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24482) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24482 : ℝ)^2 / (mW 12241 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2113917/1000000000000))/2) * ((1-firstRatio 24482) * √(1-firstRatio 24482) *
      sixthConstant (e1CovarianceRatio 24482 (mW 12241) (1/10^6) rowEps))) /
    (712/10000 - 24482*(1+1/10^6)*((2113917/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24482 (mW 12241) /
    ((1/10^5) * ((mW 12241 : ℝ)*24482*((mW 12241 : ℝ)+24482+1)))^2 +
  8*(mW 12241 : ℝ)*24482*(24482+2)*(24482+3) /
    ((1/1000)*((mW 12241 : ℝ)*24482*(24482+2)))^2 +
  covarianceVarianceBound 24482 (mW 12241) /
    ((1/1000)*covarianceMeanBound 24482 (mW 12241))^2 +
  normVarianceBound 24482 (mW 12241) / (3*inputVarianceMean 24482 (mW 12241))^2

end BstLean.Part260.Row12241
#eval (do IO.println s!"P260 END 12241 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12242 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12242
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12242 = 202994052180685 := by
  have hu : mW 12242 ≤ 202994052180685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12242 ≤ 202994052180684 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12242)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24484 ^ 2)
    ((12500000000000000000/1922968863262312441267487))
    ((25000000000000000000/3845780646891945392860809)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24484) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24484 : ℝ)^2 / (mW 12242 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2113743/1000000000000))/2) * ((1-firstRatio 24484) * √(1-firstRatio 24484) *
      sixthConstant (e1CovarianceRatio 24484 (mW 12242) (1/10^6) rowEps))) /
    (712/10000 - 24484*(1+1/10^6)*((2113743/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24484 (mW 12242) /
    ((1/10^5) * ((mW 12242 : ℝ)*24484*((mW 12242 : ℝ)+24484+1)))^2 +
  8*(mW 12242 : ℝ)*24484*(24484+2)*(24484+3) /
    ((1/1000)*((mW 12242 : ℝ)*24484*(24484+2)))^2 +
  covarianceVarianceBound 24484 (mW 12242) /
    ((1/1000)*covarianceMeanBound 24484 (mW 12242))^2 +
  normVarianceBound 24484 (mW 12242) / (3*inputVarianceMean 24484 (mW 12242))^2

end BstLean.Part260.Row12242
#eval (do IO.println s!"P260 END 12242 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12243 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12243
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12243 = 203052094308674 := by
  have hu : mW 12243 ≤ 203052094308674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12243 ≤ 203052094308673 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12243)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24486 ^ 2)
    ((25000000000000000000/3846251885789983861858821))
    ((5000000000000000000/769218961231460874436931)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24486) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24486 : ℝ)^2 / (mW 12243 : ℝ)) * (1 + 1/10^6)^2 *
    √(((66049/31250000000))/2) * ((1-firstRatio 24486) * √(1-firstRatio 24486) *
      sixthConstant (e1CovarianceRatio 24486 (mW 12243) (1/10^6) rowEps))) /
    (712/10000 - 24486*(1+1/10^6)*((66049/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24486 (mW 12243) /
    ((1/10^5) * ((mW 12243 : ℝ)*24486*((mW 12243 : ℝ)+24486+1)))^2 +
  8*(mW 12243 : ℝ)*24486*(24486+2)*(24486+3) /
    ((1/1000)*((mW 12243 : ℝ)*24486*(24486+2)))^2 +
  covarianceVarianceBound 24486 (mW 12243) /
    ((1/1000)*covarianceMeanBound 24486 (mW 12243))^2 +
  normVarianceBound 24486 (mW 12243) / (3*inputVarianceMean 24486 (mW 12243))^2

end BstLean.Part260.Row12243
#eval (do IO.println s!"P260 END 12243 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12244 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12244
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12244 = 203110148289979 := by
  have hu : mW 12244 ≤ 203110148289979 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12244 ≤ 203110148289978 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12244)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24488 ^ 2)
    ((6250000000000000000/961641511263835710295667))
    ((25000000000000000000/3846408965422663351508501)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24488) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24488 : ℝ)^2 / (mW 12244 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2113393/1000000000000))/2) * ((1-firstRatio 24488) * √(1-firstRatio 24488) *
      sixthConstant (e1CovarianceRatio 24488 (mW 12244) (1/10^6) rowEps))) /
    (712/10000 - 24488*(1+1/10^6)*((2113393/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24488 (mW 12244) /
    ((1/10^5) * ((mW 12244 : ℝ)*24488*((mW 12244 : ℝ)+24488+1)))^2 +
  8*(mW 12244 : ℝ)*24488*(24488+2)*(24488+3) /
    ((1/1000)*((mW 12244 : ℝ)*24488*(24488+2)))^2 +
  covarianceVarianceBound 24488 (mW 12244) /
    ((1/1000)*covarianceMeanBound 24488 (mW 12244))^2 +
  normVarianceBound 24488 (mW 12244) / (3*inputVarianceMean 24488 (mW 12244))^2

end BstLean.Part260.Row12244
#eval (do IO.println s!"P260 END 12244 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12245 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12245
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12245 = 203168214126051 := by
  have hu : mW 12245 ≤ 203168214126051 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12245 ≤ 203168214126050 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12245)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24490 ^ 2)
    ((5000000000000000000/769376040864140364101303))
    ((25000000000000000000/3846723124688022330832347)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24490) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24490 : ℝ)^2 / (mW 12245 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2113219/1000000000000))/2) * ((1-firstRatio 24490) * √(1-firstRatio 24490) *
      sixthConstant (e1CovarianceRatio 24490 (mW 12245) (1/10^6) rowEps))) /
    (712/10000 - 24490*(1+1/10^6)*((2113219/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24490 (mW 12245) /
    ((1/10^5) * ((mW 12245 : ℝ)*24490*((mW 12245 : ℝ)+24490+1)))^2 +
  8*(mW 12245 : ℝ)*24490*(24490+2)*(24490+3) /
    ((1/1000)*((mW 12245 : ℝ)*24490*(24490+2)))^2 +
  covarianceVarianceBound 24490 (mW 12245) /
    ((1/1000)*covarianceMeanBound 24490 (mW 12245))^2 +
  normVarianceBound 24490 (mW 12245) / (3*inputVarianceMean 24490 (mW 12245))^2

end BstLean.Part260.Row12245
#eval (do IO.println s!"P260 END 12245 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12246 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12246
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12246 = 203226291818342 := by
  have hu : mW 12246 ≤ 203226291818342 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12246 ≤ 203226291818341 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12246)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24492 ^ 2)
    ((12500000000000000000/1923597181793030399915181))
    ((25000000000000000000/3847037283953381310156193)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24492) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24492 : ℝ)^2 / (mW 12246 : ℝ)) * (1 + 1/10^6)^2 *
    √(((528261/250000000000))/2) * ((1-firstRatio 24492) * √(1-firstRatio 24492) *
      sixthConstant (e1CovarianceRatio 24492 (mW 12246) (1/10^6) rowEps))) /
    (712/10000 - 24492*(1+1/10^6)*((528261/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24492 (mW 12246) /
    ((1/10^5) * ((mW 12246 : ℝ)*24492*((mW 12246 : ℝ)+24492+1)))^2 +
  8*(mW 12246 : ℝ)*24492*(24492+2)*(24492+3) /
    ((1/1000)*((mW 12246 : ℝ)*24492*(24492+2)))^2 +
  covarianceVarianceBound 24492 (mW 12246) /
    ((1/1000)*covarianceMeanBound 24492 (mW 12246))^2 +
  normVarianceBound 24492 (mW 12246) / (3*inputVarianceMean 24492 (mW 12246))^2

end BstLean.Part260.Row12246
#eval (do IO.println s!"P260 END 12246 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12247 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12247
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12247 = 203284381368306 := by
  have hu : mW 12247 ≤ 203284381368306 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12247 ≤ 203284381368305 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12247)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24494 ^ 2)
    ((25000000000000000000/3847508522851419779154209))
    ((25000000000000000000/3847351443218740289480039)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24494) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24494 : ℝ)^2 / (mW 12247 : ℝ)) * (1 + 1/10^6)^2 *
    √(((211287/100000000000))/2) * ((1-firstRatio 24494) * √(1-firstRatio 24494) *
      sixthConstant (e1CovarianceRatio 24494 (mW 12247) (1/10^6) rowEps))) /
    (712/10000 - 24494*(1+1/10^6)*((211287/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24494 (mW 12247) /
    ((1/10^5) * ((mW 12247 : ℝ)*24494*((mW 12247 : ℝ)+24494+1)))^2 +
  8*(mW 12247 : ℝ)*24494*(24494+2)*(24494+3) /
    ((1/1000)*((mW 12247 : ℝ)*24494*(24494+2)))^2 +
  covarianceVarianceBound 24494 (mW 12247) /
    ((1/1000)*covarianceMeanBound 24494 (mW 12247))^2 +
  normVarianceBound 24494 (mW 12247) / (3*inputVarianceMean 24494 (mW 12247))^2

end BstLean.Part260.Row12247
#eval (do IO.println s!"P260 END 12247 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12248 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12248
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12248 = 203342482777394 := by
  have hu : mW 12248 ≤ 203342482777394 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12248 ≤ 203342482777393 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12248)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24496 ^ 2)
    ((3125000000000000000/480977835264597344809757))
    ((5000000000000000000/769533120496819853760777)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24496) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24496 : ℝ)^2 / (mW 12248 : ℝ)) * (1 + 1/10^6)^2 *
    √(((264087/125000000000))/2) * ((1-firstRatio 24496) * √(1-firstRatio 24496) *
      sixthConstant (e1CovarianceRatio 24496 (mW 12248) (1/10^6) rowEps))) /
    (712/10000 - 24496*(1+1/10^6)*((264087/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24496 (mW 12248) /
    ((1/10^5) * ((mW 12248 : ℝ)*24496*((mW 12248 : ℝ)+24496+1)))^2 +
  8*(mW 12248 : ℝ)*24496*(24496+2)*(24496+3) /
    ((1/1000)*((mW 12248 : ℝ)*24496*(24496+2)))^2 +
  covarianceVarianceBound 24496 (mW 12248) /
    ((1/1000)*covarianceMeanBound 24496 (mW 12248))^2 +
  normVarianceBound 24496 (mW 12248) / (3*inputVarianceMean 24496 (mW 12248))^2

end BstLean.Part260.Row12248
#eval (do IO.println s!"P260 END 12248 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12249 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12249
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12249 = 203400596047059 := by
  have hu : mW 12249 ≤ 203400596047059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12249 ≤ 203400596047058 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12249)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24498 ^ 2)
    ((25000000000000000000/3848136841382137737801903))
    ((25000000000000000000/3847979761749458248127731)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24498) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24498 : ℝ)^2 / (mW 12249 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2112521/1000000000000))/2) * ((1-firstRatio 24498) * √(1-firstRatio 24498) *
      sixthConstant (e1CovarianceRatio 24498 (mW 12249) (1/10^6) rowEps))) /
    (712/10000 - 24498*(1+1/10^6)*((2112521/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24498 (mW 12249) /
    ((1/10^5) * ((mW 12249 : ℝ)*24498*((mW 12249 : ℝ)+24498+1)))^2 +
  8*(mW 12249 : ℝ)*24498*(24498+2)*(24498+3) /
    ((1/1000)*((mW 12249 : ℝ)*24498*(24498+2)))^2 +
  covarianceVarianceBound 24498 (mW 12249) /
    ((1/1000)*covarianceMeanBound 24498 (mW 12249))^2 +
  normVarianceBound 24498 (mW 12249) / (3*inputVarianceMean 24498 (mW 12249))^2

end BstLean.Part260.Row12249
#eval (do IO.println s!"P260 END 12249 0 {← IO.monoMsNow}" : IO Unit)
