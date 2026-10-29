import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part259Data10
import BstLean.Part259Data11
import BstLean.Part259Data12
import BstLean.Part259Data13
import BstLean.Part259Data14
#eval (do IO.println s!"P260 START 12275 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12275
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12275 = 204915708880779 := by
  have hu : mW 12275 ≤ 204915708880779 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12275 ≤ 204915708880778 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12275)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24550 ^ 2)
    ((1000000000000000000/154252199291258848008877))
    ((25000000000000000000/3856147902648791710547727)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24550) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24550 : ℝ)^2 / (mW 12275 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2107997/1000000000000))/2) * ((1-firstRatio 24550) * √(1-firstRatio 24550) *
      sixthConstant (e1CovarianceRatio 24550 (mW 12275) (1/10^6) rowEps))) /
    (712/10000 - 24550*(1+1/10^6)*((2107997/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24550 (mW 12275) /
    ((1/10^5) * ((mW 12275 : ℝ)*24550*((mW 12275 : ℝ)+24550+1)))^2 +
  8*(mW 12275 : ℝ)*24550*(24550+2)*(24550+3) /
    ((1/1000)*((mW 12275 : ℝ)*24550*(24550+2)))^2 +
  covarianceVarianceBound 24550 (mW 12275) /
    ((1/1000)*covarianceMeanBound 24550 (mW 12275))^2 +
  normVarianceBound 24550 (mW 12275) / (3*inputVarianceMean 24550 (mW 12275))^2

end BstLean.Part260.Row12275
#eval (do IO.println s!"P260 END 12275 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12276 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12276
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12276 = 204974142935296 := by
  have hu : mW 12276 ≤ 204974142935296 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12276 ≤ 204974142935295 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12276)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24552 ^ 2)
    ((6250000000000000000/964154785386707544886443))
    ((25000000000000000000/3856462061914150689871573)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24552) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24552 : ℝ)^2 / (mW 12276 : ℝ)) * (1 + 1/10^6)^2 *
    √(((131739/62500000000))/2) * ((1-firstRatio 24552) * √(1-firstRatio 24552) *
      sixthConstant (e1CovarianceRatio 24552 (mW 12276) (1/10^6) rowEps))) /
    (712/10000 - 24552*(1+1/10^6)*((131739/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24552 (mW 12276) /
    ((1/10^5) * ((mW 12276 : ℝ)*24552*((mW 12276 : ℝ)+24552+1)))^2 +
  8*(mW 12276 : ℝ)*24552*(24552+2)*(24552+3) /
    ((1/1000)*((mW 12276 : ℝ)*24552*(24552+2)))^2 +
  covarianceVarianceBound 24552 (mW 12276) /
    ((1/1000)*covarianceMeanBound 24552 (mW 12276))^2 +
  normVarianceBound 24552 (mW 12276) / (3*inputVarianceMean 24552 (mW 12276))^2

end BstLean.Part260.Row12276
#eval (do IO.println s!"P260 END 12276 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12277 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12277
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12277 = 205032588891084 := by
  have hu : mW 12277 ≤ 205032588891084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12277 ≤ 205032588891083 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12277)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24554 ^ 2)
    ((25000000000000000000/3856933300812189158869619))
    ((25000000000000000000/3856776221179509669195419)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24554) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24554 : ℝ)^2 / (mW 12277 : ℝ)) * (1 + 1/10^6)^2 *
    √(((42153/20000000000))/2) * ((1-firstRatio 24554) * √(1-firstRatio 24554) *
      sixthConstant (e1CovarianceRatio 24554 (mW 12277) (1/10^6) rowEps))) /
    (712/10000 - 24554*(1+1/10^6)*((42153/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24554 (mW 12277) /
    ((1/10^5) * ((mW 12277 : ℝ)*24554*((mW 12277 : ℝ)+24554+1)))^2 +
  8*(mW 12277 : ℝ)*24554*(24554+2)*(24554+3) /
    ((1/1000)*((mW 12277 : ℝ)*24554*(24554+2)))^2 +
  covarianceVarianceBound 24554 (mW 12277) /
    ((1/1000)*covarianceMeanBound 24554 (mW 12277))^2 +
  normVarianceBound 24554 (mW 12277) / (3*inputVarianceMean 24554 (mW 12277))^2

end BstLean.Part260.Row12277
#eval (do IO.println s!"P260 END 12277 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12278 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12278
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12278 = 205091046749598 := by
  have hu : mW 12278 ≤ 205091046749598 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12278 ≤ 205091046749597 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12278)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24556 ^ 2)
    ((12500000000000000000/1928623730038774069096733))
    ((5000000000000000000/771418076088973729703853)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24556) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24556 : ℝ)^2 / (mW 12278 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2107477/1000000000000))/2) * ((1-firstRatio 24556) * √(1-firstRatio 24556) *
      sixthConstant (e1CovarianceRatio 24556 (mW 12278) (1/10^6) rowEps))) /
    (712/10000 - 24556*(1+1/10^6)*((2107477/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24556 (mW 12278) /
    ((1/10^5) * ((mW 12278 : ℝ)*24556*((mW 12278 : ℝ)+24556+1)))^2 +
  8*(mW 12278 : ℝ)*24556*(24556+2)*(24556+3) /
    ((1/1000)*((mW 12278 : ℝ)*24556*(24556+2)))^2 +
  covarianceVarianceBound 24556 (mW 12278) /
    ((1/1000)*covarianceMeanBound 24556 (mW 12278))^2 +
  normVarianceBound 24556 (mW 12278) / (3*inputVarianceMean 24556 (mW 12278))^2

end BstLean.Part260.Row12278
#eval (do IO.println s!"P260 END 12278 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12279 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12279
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12279 = 205149516512292 := by
  have hu : mW 12279 ≤ 205149516512292 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12279 ≤ 205149516512291 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12279)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24558 ^ 2)
    ((25000000000000000000/3857561619342907117517313))
    ((25000000000000000000/3857404539710227627843111)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24558) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24558 : ℝ)^2 / (mW 12279 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2107303/1000000000000))/2) * ((1-firstRatio 24558) * √(1-firstRatio 24558) *
      sixthConstant (e1CovarianceRatio 24558 (mW 12279) (1/10^6) rowEps))) /
    (712/10000 - 24558*(1+1/10^6)*((2107303/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24558 (mW 12279) /
    ((1/10^5) * ((mW 12279 : ℝ)*24558*((mW 12279 : ℝ)+24558+1)))^2 +
  8*(mW 12279 : ℝ)*24558*(24558+2)*(24558+3) /
    ((1/1000)*((mW 12279 : ℝ)*24558*(24558+2)))^2 +
  covarianceVarianceBound 24558 (mW 12279) /
    ((1/1000)*covarianceMeanBound 24558 (mW 12279))^2 +
  normVarianceBound 24558 (mW 12279) / (3*inputVarianceMean 24558 (mW 12279))^2

end BstLean.Part260.Row12279
#eval (do IO.println s!"P260 END 12279 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12280 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12280
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12280 = 205207998180622 := by
  have hu : mW 12280 ≤ 205207998180622 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12280 ≤ 205207998180621 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12280)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24560 ^ 2)
    ((625000000000000000/96446894465206652421029))
    ((25000000000000000000/3857718698975586607166957)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24560) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24560 : ℝ)^2 / (mW 12280 : ℝ)) * (1 + 1/10^6)^2 *
    √(((210713/100000000000))/2) * ((1-firstRatio 24560) * √(1-firstRatio 24560) *
      sixthConstant (e1CovarianceRatio 24560 (mW 12280) (1/10^6) rowEps))) /
    (712/10000 - 24560*(1+1/10^6)*((210713/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24560 (mW 12280) /
    ((1/10^5) * ((mW 12280 : ℝ)*24560*((mW 12280 : ℝ)+24560+1)))^2 +
  8*(mW 12280 : ℝ)*24560*(24560+2)*(24560+3) /
    ((1/1000)*((mW 12280 : ℝ)*24560*(24560+2)))^2 +
  covarianceVarianceBound 24560 (mW 12280) /
    ((1/1000)*covarianceMeanBound 24560 (mW 12280))^2 +
  normVarianceBound 24560 (mW 12280) / (3*inputVarianceMean 24560 (mW 12280))^2

end BstLean.Part260.Row12280
#eval (do IO.println s!"P260 END 12280 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12281 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12281
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12281 = 205266491756040 := by
  have hu : mW 12281 ≤ 205266491756040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12281 ≤ 205266491756039 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12281)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24562 ^ 2)
    ((25000000000000000000/3858189937873625076165007))
    ((25000000000000000000/3858032858240945586490803)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24562) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24562 : ℝ)^2 / (mW 12281 : ℝ)) * (1 + 1/10^6)^2 *
    √(((526739/250000000000))/2) * ((1-firstRatio 24562) * √(1-firstRatio 24562) *
      sixthConstant (e1CovarianceRatio 24562 (mW 12281) (1/10^6) rowEps))) /
    (712/10000 - 24562*(1+1/10^6)*((526739/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24562 (mW 12281) /
    ((1/10^5) * ((mW 12281 : ℝ)*24562*((mW 12281 : ℝ)+24562+1)))^2 +
  8*(mW 12281 : ℝ)*24562*(24562+2)*(24562+3) /
    ((1/1000)*((mW 12281 : ℝ)*24562*(24562+2)))^2 +
  covarianceVarianceBound 24562 (mW 12281) /
    ((1/1000)*covarianceMeanBound 24562 (mW 12281))^2 +
  normVarianceBound 24562 (mW 12281) / (3*inputVarianceMean 24562 (mW 12281))^2

end BstLean.Part260.Row12281
#eval (do IO.println s!"P260 END 12281 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12282 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12282
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12282 = 205324997240002 := by
  have hu : mW 12282 ≤ 205324997240002 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12282 ≤ 205324997240001 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12282)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24564 ^ 2)
    ((12500000000000000000/1929252048569492027744427))
    ((25000000000000000000/3858347017506304565814649)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24564) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24564 : ℝ)^2 / (mW 12282 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2106783/1000000000000))/2) * ((1-firstRatio 24564) * √(1-firstRatio 24564) *
      sixthConstant (e1CovarianceRatio 24564 (mW 12282) (1/10^6) rowEps))) /
    (712/10000 - 24564*(1+1/10^6)*((2106783/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24564 (mW 12282) /
    ((1/10^5) * ((mW 12282 : ℝ)*24564*((mW 12282 : ℝ)+24564+1)))^2 +
  8*(mW 12282 : ℝ)*24564*(24564+2)*(24564+3) /
    ((1/1000)*((mW 12282 : ℝ)*24564*(24564+2)))^2 +
  covarianceVarianceBound 24564 (mW 12282) /
    ((1/1000)*covarianceMeanBound 24564 (mW 12282))^2 +
  normVarianceBound 24564 (mW 12282) / (3*inputVarianceMean 24564 (mW 12282))^2

end BstLean.Part260.Row12282
#eval (do IO.println s!"P260 END 12282 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12283 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12283
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12283 = 205383514633962 := by
  have hu : mW 12283 ≤ 205383514633962 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12283 ≤ 205383514633961 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12283)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24566 ^ 2)
    ((25000000000000000000/3858818256404343034812701))
    ((5000000000000000000/771732235354332709027699)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24566) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24566 : ℝ)^2 / (mW 12283 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2106609/1000000000000))/2) * ((1-firstRatio 24566) * √(1-firstRatio 24566) *
      sixthConstant (e1CovarianceRatio 24566 (mW 12283) (1/10^6) rowEps))) /
    (712/10000 - 24566*(1+1/10^6)*((2106609/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24566 (mW 12283) /
    ((1/10^5) * ((mW 12283 : ℝ)*24566*((mW 12283 : ℝ)+24566+1)))^2 +
  8*(mW 12283 : ℝ)*24566*(24566+2)*(24566+3) /
    ((1/1000)*((mW 12283 : ℝ)*24566*(24566+2)))^2 +
  covarianceVarianceBound 24566 (mW 12283) /
    ((1/1000)*covarianceMeanBound 24566 (mW 12283))^2 +
  normVarianceBound 24566 (mW 12283) / (3*inputVarianceMean 24566 (mW 12283))^2

end BstLean.Part260.Row12283
#eval (do IO.println s!"P260 END 12283 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12284 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12284
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12284 = 205442043939374 := by
  have hu : mW 12284 ≤ 205442043939374 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12284 ≤ 205442043939373 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12284)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24568 ^ 2)
    ((6250000000000000000/964783103917425503534137))
    ((25000000000000000000/3858975336037022524462341)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24568) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24568 : ℝ)^2 / (mW 12284 : ℝ)) * (1 + 1/10^6)^2 *
    √(((526609/250000000000))/2) * ((1-firstRatio 24568) * √(1-firstRatio 24568) *
      sixthConstant (e1CovarianceRatio 24568 (mW 12284) (1/10^6) rowEps))) /
    (712/10000 - 24568*(1+1/10^6)*((526609/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24568 (mW 12284) /
    ((1/10^5) * ((mW 12284 : ℝ)*24568*((mW 12284 : ℝ)+24568+1)))^2 +
  8*(mW 12284 : ℝ)*24568*(24568+2)*(24568+3) /
    ((1/1000)*((mW 12284 : ℝ)*24568*(24568+2)))^2 +
  covarianceVarianceBound 24568 (mW 12284) /
    ((1/1000)*covarianceMeanBound 24568 (mW 12284))^2 +
  normVarianceBound 24568 (mW 12284) / (3*inputVarianceMean 24568 (mW 12284))^2

end BstLean.Part260.Row12284
#eval (do IO.println s!"P260 END 12284 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12285 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12285
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12285 = 205500585157694 := by
  have hu : mW 12285 ≤ 205500585157694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12285 ≤ 205500585157693 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12285)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24570 ^ 2)
    ((5000000000000000000/771889314987012198692079))
    ((25000000000000000000/3859289495302381503786187)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24570) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24570 : ℝ)^2 / (mW 12285 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1053131/500000000000))/2) * ((1-firstRatio 24570) * √(1-firstRatio 24570) *
      sixthConstant (e1CovarianceRatio 24570 (mW 12285) (1/10^6) rowEps))) /
    (712/10000 - 24570*(1+1/10^6)*((1053131/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24570 (mW 12285) /
    ((1/10^5) * ((mW 12285 : ℝ)*24570*((mW 12285 : ℝ)+24570+1)))^2 +
  8*(mW 12285 : ℝ)*24570*(24570+2)*(24570+3) /
    ((1/1000)*((mW 12285 : ℝ)*24570*(24570+2)))^2 +
  covarianceVarianceBound 24570 (mW 12285) /
    ((1/1000)*covarianceMeanBound 24570 (mW 12285))^2 +
  normVarianceBound 24570 (mW 12285) / (3*inputVarianceMean 24570 (mW 12285))^2

end BstLean.Part260.Row12285
#eval (do IO.println s!"P260 END 12285 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12286 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12286
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12286 = 205559138290376 := by
  have hu : mW 12286 ≤ 205559138290376 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12286 ≤ 205559138290375 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12286)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24572 ^ 2)
    ((12500000000000000000/1929880367100209986392121))
    ((25000000000000000000/3859603654567740483110033)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24572) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24572 : ℝ)^2 / (mW 12286 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2106089/1000000000000))/2) * ((1-firstRatio 24572) * √(1-firstRatio 24572) *
      sixthConstant (e1CovarianceRatio 24572 (mW 12286) (1/10^6) rowEps))) /
    (712/10000 - 24572*(1+1/10^6)*((2106089/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24572 (mW 12286) /
    ((1/10^5) * ((mW 12286 : ℝ)*24572*((mW 12286 : ℝ)+24572+1)))^2 +
  8*(mW 12286 : ℝ)*24572*(24572+2)*(24572+3) /
    ((1/1000)*((mW 12286 : ℝ)*24572*(24572+2)))^2 +
  covarianceVarianceBound 24572 (mW 12286) /
    ((1/1000)*covarianceMeanBound 24572 (mW 12286))^2 +
  normVarianceBound 24572 (mW 12286) / (3*inputVarianceMean 24572 (mW 12286))^2

end BstLean.Part260.Row12286
#eval (do IO.println s!"P260 END 12286 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12287 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12287
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12287 = 205617703338875 := by
  have hu : mW 12287 ≤ 205617703338875 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12287 ≤ 205617703338874 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12287)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24574 ^ 2)
    ((25000000000000000000/3860074893465778952108089))
    ((25000000000000000000/3859917813833099462433879)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24574) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24574 : ℝ)^2 / (mW 12287 : ℝ)) * (1 + 1/10^6)^2 *
    √(((526479/250000000000))/2) * ((1-firstRatio 24574) * √(1-firstRatio 24574) *
      sixthConstant (e1CovarianceRatio 24574 (mW 12287) (1/10^6) rowEps))) /
    (712/10000 - 24574*(1+1/10^6)*((526479/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24574 (mW 12287) /
    ((1/10^5) * ((mW 12287 : ℝ)*24574*((mW 12287 : ℝ)+24574+1)))^2 +
  8*(mW 12287 : ℝ)*24574*(24574+2)*(24574+3) /
    ((1/1000)*((mW 12287 : ℝ)*24574*(24574+2)))^2 +
  covarianceVarianceBound 24574 (mW 12287) /
    ((1/1000)*covarianceMeanBound 24574 (mW 12287))^2 +
  normVarianceBound 24574 (mW 12287) / (3*inputVarianceMean 24574 (mW 12287))^2

end BstLean.Part260.Row12287
#eval (do IO.println s!"P260 END 12287 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12288 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12288
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12288 = 205676280304646 := by
  have hu : mW 12288 ≤ 205676280304646 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12288 ≤ 205676280304645 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12288)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24576 ^ 2)
    ((6103515625000000/942477796076937971541))
    ((1000000000000000000/154409278923938337670309)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24576) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24576 : ℝ)^2 / (mW 12288 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2105743/1000000000000))/2) * ((1-firstRatio 24576) * √(1-firstRatio 24576) *
      sixthConstant (e1CovarianceRatio 24576 (mW 12288) (1/10^6) rowEps))) /
    (712/10000 - 24576*(1+1/10^6)*((2105743/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24576 (mW 12288) /
    ((1/10^5) * ((mW 12288 : ℝ)*24576*((mW 12288 : ℝ)+24576+1)))^2 +
  8*(mW 12288 : ℝ)*24576*(24576+2)*(24576+3) /
    ((1/1000)*((mW 12288 : ℝ)*24576*(24576+2)))^2 +
  covarianceVarianceBound 24576 (mW 12288) /
    ((1/1000)*covarianceMeanBound 24576 (mW 12288))^2 +
  normVarianceBound 24576 (mW 12288) / (3*inputVarianceMean 24576 (mW 12288))^2

end BstLean.Part260.Row12288
#eval (do IO.println s!"P260 END 12288 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12289 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12289
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12289 = 205734869189143 := by
  have hu : mW 12289 ≤ 205734869189143 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12289 ≤ 205734869189142 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12289)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24578 ^ 2)
    ((25000000000000000000/3860703211996496910755783))
    ((25000000000000000000/3860546132363817421081571)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24578) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24578 : ℝ)^2 / (mW 12289 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2105569/1000000000000))/2) * ((1-firstRatio 24578) * √(1-firstRatio 24578) *
      sixthConstant (e1CovarianceRatio 24578 (mW 12289) (1/10^6) rowEps))) /
    (712/10000 - 24578*(1+1/10^6)*((2105569/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24578 (mW 12289) /
    ((1/10^5) * ((mW 12289 : ℝ)*24578*((mW 12289 : ℝ)+24578+1)))^2 +
  8*(mW 12289 : ℝ)*24578*(24578+2)*(24578+3) /
    ((1/1000)*((mW 12289 : ℝ)*24578*(24578+2)))^2 +
  covarianceVarianceBound 24578 (mW 12289) /
    ((1/1000)*covarianceMeanBound 24578 (mW 12289))^2 +
  normVarianceBound 24578 (mW 12289) / (3*inputVarianceMean 24578 (mW 12289))^2

end BstLean.Part260.Row12289
#eval (do IO.println s!"P260 END 12289 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12290 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12290
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12290 = 205793469993822 := by
  have hu : mW 12290 ≤ 205793469993822 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12290 ≤ 205793469993821 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12290)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24580 ^ 2)
    ((2500000000000000000/386101737126185589007963))
    ((25000000000000000000/3860860291629176400405417)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24580) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24580 : ℝ)^2 / (mW 12290 : ℝ)) * (1 + 1/10^6)^2 *
    √(((526349/250000000000))/2) * ((1-firstRatio 24580) * √(1-firstRatio 24580) *
      sixthConstant (e1CovarianceRatio 24580 (mW 12290) (1/10^6) rowEps))) /
    (712/10000 - 24580*(1+1/10^6)*((526349/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24580 (mW 12290) /
    ((1/10^5) * ((mW 12290 : ℝ)*24580*((mW 12290 : ℝ)+24580+1)))^2 +
  8*(mW 12290 : ℝ)*24580*(24580+2)*(24580+3) /
    ((1/1000)*((mW 12290 : ℝ)*24580*(24580+2)))^2 +
  covarianceVarianceBound 24580 (mW 12290) /
    ((1/1000)*covarianceMeanBound 24580 (mW 12290))^2 +
  normVarianceBound 24580 (mW 12290) / (3*inputVarianceMean 24580 (mW 12290))^2

end BstLean.Part260.Row12290
#eval (do IO.println s!"P260 END 12290 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12291 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12291
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12291 = 205852082720137 := by
  have hu : mW 12291 ≤ 205852082720137 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12291 ≤ 205852082720136 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12291)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24582 ^ 2)
    ((25000000000000000000/3861331530527214869403477))
    ((25000000000000000000/3861174450894535379729263)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24582) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24582 : ℝ)^2 / (mW 12291 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2105223/1000000000000))/2) * ((1-firstRatio 24582) * √(1-firstRatio 24582) *
      sixthConstant (e1CovarianceRatio 24582 (mW 12291) (1/10^6) rowEps))) /
    (712/10000 - 24582*(1+1/10^6)*((2105223/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24582 (mW 12291) /
    ((1/10^5) * ((mW 12291 : ℝ)*24582*((mW 12291 : ℝ)+24582+1)))^2 +
  8*(mW 12291 : ℝ)*24582*(24582+2)*(24582+3) /
    ((1/1000)*((mW 12291 : ℝ)*24582*(24582+2)))^2 +
  covarianceVarianceBound 24582 (mW 12291) /
    ((1/1000)*covarianceMeanBound 24582 (mW 12291))^2 +
  normVarianceBound 24582 (mW 12291) / (3*inputVarianceMean 24582 (mW 12291))^2

end BstLean.Part260.Row12291
#eval (do IO.println s!"P260 END 12291 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12292 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12292
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12292 = 205910707369544 := by
  have hu : mW 12292 ≤ 205910707369544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12292 ≤ 205910707369543 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12292)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24584 ^ 2)
    ((6250000000000000000/965411422448143462181831))
    ((25000000000000000000/3861488610159894359053109)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24584) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24584 : ℝ)^2 / (mW 12292 : ℝ)) * (1 + 1/10^6)^2 *
    √(((42101/20000000000))/2) * ((1-firstRatio 24584) * √(1-firstRatio 24584) *
      sixthConstant (e1CovarianceRatio 24584 (mW 12292) (1/10^6) rowEps))) /
    (712/10000 - 24584*(1+1/10^6)*((42101/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24584 (mW 12292) /
    ((1/10^5) * ((mW 12292 : ℝ)*24584*((mW 12292 : ℝ)+24584+1)))^2 +
  8*(mW 12292 : ℝ)*24584*(24584+2)*(24584+3) /
    ((1/1000)*((mW 12292 : ℝ)*24584*(24584+2)))^2 +
  covarianceVarianceBound 24584 (mW 12292) /
    ((1/1000)*covarianceMeanBound 24584 (mW 12292))^2 +
  normVarianceBound 24584 (mW 12292) / (3*inputVarianceMean 24584 (mW 12292))^2

end BstLean.Part260.Row12292
#eval (do IO.println s!"P260 END 12292 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12293 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12293
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12293 = 205969343943498 := by
  have hu : mW 12293 ≤ 205969343943498 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12293 ≤ 205969343943497 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12293)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24586 ^ 2)
    ((25000000000000000000/3861959849057932828051171))
    ((5000000000000000000/772360553885050667675391)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24586) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24586 : ℝ)^2 / (mW 12293 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2104877/1000000000000))/2) * ((1-firstRatio 24586) * √(1-firstRatio 24586) *
      sixthConstant (e1CovarianceRatio 24586 (mW 12293) (1/10^6) rowEps))) /
    (712/10000 - 24586*(1+1/10^6)*((2104877/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24586 (mW 12293) /
    ((1/10^5) * ((mW 12293 : ℝ)*24586*((mW 12293 : ℝ)+24586+1)))^2 +
  8*(mW 12293 : ℝ)*24586*(24586+2)*(24586+3) /
    ((1/1000)*((mW 12293 : ℝ)*24586*(24586+2)))^2 +
  covarianceVarianceBound 24586 (mW 12293) /
    ((1/1000)*covarianceMeanBound 24586 (mW 12293))^2 +
  normVarianceBound 24586 (mW 12293) / (3*inputVarianceMean 24586 (mW 12293))^2

end BstLean.Part260.Row12293
#eval (do IO.println s!"P260 END 12293 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12294 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12294
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12294 = 206027992443454 := by
  have hu : mW 12294 ≤ 206027992443454 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12294 ≤ 206027992443453 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12294)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24588 ^ 2)
    ((12500000000000000000/1931137004161645903687509))
    ((25000000000000000000/3862116928690612317700801)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24588) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24588 : ℝ)^2 / (mW 12294 : ℝ)) * (1 + 1/10^6)^2 *
    √(((16443/7812500000))/2) * ((1-firstRatio 24588) * √(1-firstRatio 24588) *
      sixthConstant (e1CovarianceRatio 24588 (mW 12294) (1/10^6) rowEps))) /
    (712/10000 - 24588*(1+1/10^6)*((16443/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24588 (mW 12294) /
    ((1/10^5) * ((mW 12294 : ℝ)*24588*((mW 12294 : ℝ)+24588+1)))^2 +
  8*(mW 12294 : ℝ)*24588*(24588+2)*(24588+3) /
    ((1/1000)*((mW 12294 : ℝ)*24588*(24588+2)))^2 +
  covarianceVarianceBound 24588 (mW 12294) /
    ((1/1000)*covarianceMeanBound 24588 (mW 12294))^2 +
  normVarianceBound 24588 (mW 12294) / (3*inputVarianceMean 24588 (mW 12294))^2

end BstLean.Part260.Row12294
#eval (do IO.println s!"P260 END 12294 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12295 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12295
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12295 = 206086652870866 := by
  have hu : mW 12295 ≤ 206086652870866 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12295 ≤ 206086652870865 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12295)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24590 ^ 2)
    ((5000000000000000000/772517633517730157339773))
    ((25000000000000000000/3862431087955971297024647)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24590) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24590 : ℝ)^2 / (mW 12295 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2104531/1000000000000))/2) * ((1-firstRatio 24590) * √(1-firstRatio 24590) *
      sixthConstant (e1CovarianceRatio 24590 (mW 12295) (1/10^6) rowEps))) /
    (712/10000 - 24590*(1+1/10^6)*((2104531/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24590 (mW 12295) /
    ((1/10^5) * ((mW 12295 : ℝ)*24590*((mW 12295 : ℝ)+24590+1)))^2 +
  8*(mW 12295 : ℝ)*24590*(24590+2)*(24590+3) /
    ((1/1000)*((mW 12295 : ℝ)*24590*(24590+2)))^2 +
  covarianceVarianceBound 24590 (mW 12295) /
    ((1/1000)*covarianceMeanBound 24590 (mW 12295))^2 +
  normVarianceBound 24590 (mW 12295) / (3*inputVarianceMean 24590 (mW 12295))^2

end BstLean.Part260.Row12295
#eval (do IO.println s!"P260 END 12295 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12296 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12296
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12296 = 206145325227192 := by
  have hu : mW 12296 ≤ 206145325227192 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12296 ≤ 206145325227191 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12296)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24592 ^ 2)
    ((3125000000000000000/482862790856751220752839))
    ((25000000000000000000/3862745247221330276348493)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24592) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24592 : ℝ)^2 / (mW 12296 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1052179/500000000000))/2) * ((1-firstRatio 24592) * √(1-firstRatio 24592) *
      sixthConstant (e1CovarianceRatio 24592 (mW 12296) (1/10^6) rowEps))) /
    (712/10000 - 24592*(1+1/10^6)*((1052179/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24592 (mW 12296) /
    ((1/10^5) * ((mW 12296 : ℝ)*24592*((mW 12296 : ℝ)+24592+1)))^2 +
  8*(mW 12296 : ℝ)*24592*(24592+2)*(24592+3) /
    ((1/1000)*((mW 12296 : ℝ)*24592*(24592+2)))^2 +
  covarianceVarianceBound 24592 (mW 12296) /
    ((1/1000)*covarianceMeanBound 24592 (mW 12296))^2 +
  normVarianceBound 24592 (mW 12296) / (3*inputVarianceMean 24592 (mW 12296))^2

end BstLean.Part260.Row12296
#eval (do IO.println s!"P260 END 12296 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12297 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12297
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12297 = 206204009513885 := by
  have hu : mW 12297 ≤ 206204009513885 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12297 ≤ 206204009513884 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12297)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24594 ^ 2)
    ((25000000000000000000/3863216486119368745346559))
    ((25000000000000000000/3863059406486689255672339)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24594) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24594 : ℝ)^2 / (mW 12297 : ℝ)) * (1 + 1/10^6)^2 *
    √(((420837/200000000000))/2) * ((1-firstRatio 24594) * √(1-firstRatio 24594) *
      sixthConstant (e1CovarianceRatio 24594 (mW 12297) (1/10^6) rowEps))) /
    (712/10000 - 24594*(1+1/10^6)*((420837/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24594 (mW 12297) /
    ((1/10^5) * ((mW 12297 : ℝ)*24594*((mW 12297 : ℝ)+24594+1)))^2 +
  8*(mW 12297 : ℝ)*24594*(24594+2)*(24594+3) /
    ((1/1000)*((mW 12297 : ℝ)*24594*(24594+2)))^2 +
  covarianceVarianceBound 24594 (mW 12297) /
    ((1/1000)*covarianceMeanBound 24594 (mW 12297))^2 +
  normVarianceBound 24594 (mW 12297) / (3*inputVarianceMean 24594 (mW 12297))^2

end BstLean.Part260.Row12297
#eval (do IO.println s!"P260 END 12297 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12298 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12298
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12298 = 206262705732401 := by
  have hu : mW 12298 ≤ 206262705732401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12298 ≤ 206262705732400 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12298)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24596 ^ 2)
    ((12500000000000000000/1931765322692363862335203))
    ((5000000000000000000/772674713150409646999237)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24596) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24596 : ℝ)^2 / (mW 12298 : ℝ)) * (1 + 1/10^6)^2 *
    √(((526003/250000000000))/2) * ((1-firstRatio 24596) * √(1-firstRatio 24596) *
      sixthConstant (e1CovarianceRatio 24596 (mW 12298) (1/10^6) rowEps))) /
    (712/10000 - 24596*(1+1/10^6)*((526003/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24596 (mW 12298) /
    ((1/10^5) * ((mW 12298 : ℝ)*24596*((mW 12298 : ℝ)+24596+1)))^2 +
  8*(mW 12298 : ℝ)*24596*(24596+2)*(24596+3) /
    ((1/1000)*((mW 12298 : ℝ)*24596*(24596+2)))^2 +
  covarianceVarianceBound 24596 (mW 12298) /
    ((1/1000)*covarianceMeanBound 24596 (mW 12298))^2 +
  normVarianceBound 24596 (mW 12298) / (3*inputVarianceMean 24596 (mW 12298))^2

end BstLean.Part260.Row12298
#eval (do IO.println s!"P260 END 12298 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12299 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12299
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12299 = 206321413884197 := by
  have hu : mW 12299 ≤ 206321413884197 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12299 ≤ 206321413884196 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12299)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24598 ^ 2)
    ((25000000000000000000/3863844804650086703994253))
    ((25000000000000000000/3863687725017407214320031)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24598) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24598 : ℝ)^2 / (mW 12299 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2103839/1000000000000))/2) * ((1-firstRatio 24598) * √(1-firstRatio 24598) *
      sixthConstant (e1CovarianceRatio 24598 (mW 12299) (1/10^6) rowEps))) /
    (712/10000 - 24598*(1+1/10^6)*((2103839/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24598 (mW 12299) /
    ((1/10^5) * ((mW 12299 : ℝ)*24598*((mW 12299 : ℝ)+24598+1)))^2 +
  8*(mW 12299 : ℝ)*24598*(24598+2)*(24598+3) /
    ((1/1000)*((mW 12299 : ℝ)*24598*(24598+2)))^2 +
  covarianceVarianceBound 24598 (mW 12299) /
    ((1/1000)*covarianceMeanBound 24598 (mW 12299))^2 +
  normVarianceBound 24598 (mW 12299) / (3*inputVarianceMean 24598 (mW 12299))^2

end BstLean.Part260.Row12299
#eval (do IO.println s!"P260 END 12299 0 {← IO.monoMsNow}" : IO Unit)
