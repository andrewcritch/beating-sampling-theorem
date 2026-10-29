import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part259Data20
import BstLean.Part259Data21
import BstLean.Part259Data22
import BstLean.Part259Data23
import BstLean.Part259Data24
#eval (do IO.println s!"P260 START 12325 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12325
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12325 = 207852019181296 := by
  have hu : mW 12325 ≤ 207852019181296 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12325 ≤ 207852019181295 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12325)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24650 ^ 2)
    ((1000000000000000000/154880517821976806656571))
    ((25000000000000000000/3871855865916740676740027)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24650) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24650 : ℝ)^2 / (mW 12325 : ℝ)) * (1 + 1/10^6)^2 *
    √(((262419/125000000000))/2) * ((1-firstRatio 24650) * √(1-firstRatio 24650) *
      sixthConstant (e1CovarianceRatio 24650 (mW 12325) (1/10^6) rowEps))) /
    (712/10000 - 24650*(1+1/10^6)*((262419/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24650 (mW 12325) /
    ((1/10^5) * ((mW 12325 : ℝ)*24650*((mW 12325 : ℝ)+24650+1)))^2 +
  8*(mW 12325 : ℝ)*24650*(24650+2)*(24650+3) /
    ((1/1000)*((mW 12325 : ℝ)*24650*(24650+2)))^2 +
  covarianceVarianceBound 24650 (mW 12325) /
    ((1/1000)*covarianceMeanBound 24650 (mW 12325))^2 +
  normVarianceBound 24650 (mW 12325) / (3*inputVarianceMean 24650 (mW 12325))^2

end BstLean.Part260.Row12325
#eval (do IO.println s!"P260 END 12325 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12326 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12326
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12326 = 207911050082008 := by
  have hu : mW 12326 ≤ 207911050082008 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12326 ≤ 207911050082007 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12326)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24652 ^ 2)
    ((12500000000000000000/1936163552407389572869061))
    ((25000000000000000000/3872170025182099656063873)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24652) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24652 : ℝ)^2 / (mW 12326 : ℝ)) * (1 + 1/10^6)^2 *
    √(((104959/50000000000))/2) * ((1-firstRatio 24652) * √(1-firstRatio 24652) *
      sixthConstant (e1CovarianceRatio 24652 (mW 12326) (1/10^6) rowEps))) /
    (712/10000 - 24652*(1+1/10^6)*((104959/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24652 (mW 12326) /
    ((1/10^5) * ((mW 12326 : ℝ)*24652*((mW 12326 : ℝ)+24652+1)))^2 +
  8*(mW 12326 : ℝ)*24652*(24652+2)*(24652+3) /
    ((1/1000)*((mW 12326 : ℝ)*24652*(24652+2)))^2 +
  covarianceVarianceBound 24652 (mW 12326) /
    ((1/1000)*covarianceMeanBound 24652 (mW 12326))^2 +
  normVarianceBound 24652 (mW 12326) / (3*inputVarianceMean 24652 (mW 12326))^2

end BstLean.Part260.Row12326
#eval (do IO.println s!"P260 END 12326 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12327 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12327
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12327 = 207970092956776 := by
  have hu : mW 12327 ≤ 207970092956776 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12327 ≤ 207970092956775 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12327)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24654 ^ 2)
    ((25000000000000000000/3872641264080138125061969))
    ((25000000000000000000/3872484184447458635387719)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24654) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24654 : ℝ)^2 / (mW 12327 : ℝ)) * (1 + 1/10^6)^2 *
    √(((32797/15625000000))/2) * ((1-firstRatio 24654) * √(1-firstRatio 24654) *
      sixthConstant (e1CovarianceRatio 24654 (mW 12327) (1/10^6) rowEps))) /
    (712/10000 - 24654*(1+1/10^6)*((32797/15625000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24654 (mW 12327) /
    ((1/10^5) * ((mW 12327 : ℝ)*24654*((mW 12327 : ℝ)+24654+1)))^2 +
  8*(mW 12327 : ℝ)*24654*(24654+2)*(24654+3) /
    ((1/1000)*((mW 12327 : ℝ)*24654*(24654+2)))^2 +
  covarianceVarianceBound 24654 (mW 12327) /
    ((1/1000)*covarianceMeanBound 24654 (mW 12327))^2 +
  normVarianceBound 24654 (mW 12327) / (3*inputVarianceMean 24654 (mW 12327))^2

end BstLean.Part260.Row12327
#eval (do IO.println s!"P260 END 12327 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12328 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12328
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12328 = 208029147807057 := by
  have hu : mW 12328 ≤ 208029147807057 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12328 ≤ 208029147807056 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12328)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24656 ^ 2)
    ((3125000000000000000/484119427918187138048227))
    ((5000000000000000000/774559668742563522942313)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24656) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24656 : ℝ)^2 / (mW 12328 : ℝ)) * (1 + 1/10^6)^2 *
    √(((419767/200000000000))/2) * ((1-firstRatio 24656) * √(1-firstRatio 24656) *
      sixthConstant (e1CovarianceRatio 24656 (mW 12328) (1/10^6) rowEps))) /
    (712/10000 - 24656*(1+1/10^6)*((419767/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24656 (mW 12328) /
    ((1/10^5) * ((mW 12328 : ℝ)*24656*((mW 12328 : ℝ)+24656+1)))^2 +
  8*(mW 12328 : ℝ)*24656*(24656+2)*(24656+3) /
    ((1/1000)*((mW 12328 : ℝ)*24656*(24656+2)))^2 +
  covarianceVarianceBound 24656 (mW 12328) /
    ((1/1000)*covarianceMeanBound 24656 (mW 12328))^2 +
  normVarianceBound 24656 (mW 12328) / (3*inputVarianceMean 24656 (mW 12328))^2

end BstLean.Part260.Row12328
#eval (do IO.println s!"P260 END 12328 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12329 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12329
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12329 = 208088214634310 := by
  have hu : mW 12329 ≤ 208088214634310 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12329 ≤ 208088214634309 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12329)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24658 ^ 2)
    ((25000000000000000000/3873269582610856083709663))
    ((25000000000000000000/3873112502978176594035411)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24658) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24658 : ℝ)^2 / (mW 12329 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2098663/1000000000000))/2) * ((1-firstRatio 24658) * √(1-firstRatio 24658) *
      sixthConstant (e1CovarianceRatio 24658 (mW 12329) (1/10^6) rowEps))) /
    (712/10000 - 24658*(1+1/10^6)*((2098663/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24658 (mW 12329) /
    ((1/10^5) * ((mW 12329 : ℝ)*24658*((mW 12329 : ℝ)+24658+1)))^2 +
  8*(mW 12329 : ℝ)*24658*(24658+2)*(24658+3) /
    ((1/1000)*((mW 12329 : ℝ)*24658*(24658+2)))^2 +
  covarianceVarianceBound 24658 (mW 12329) /
    ((1/1000)*covarianceMeanBound 24658 (mW 12329))^2 +
  normVarianceBound 24658 (mW 12329) / (3*inputVarianceMean 24658 (mW 12329))^2

end BstLean.Part260.Row12329
#eval (do IO.println s!"P260 END 12329 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12330 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12330
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12330 = 208147293439990 := by
  have hu : mW 12330 ≤ 208147293439990 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12330 ≤ 208147293439989 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12330)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24660 ^ 2)
    ((2500000000000000000/387358374187621506303351))
    ((25000000000000000000/3873426662243535573359257)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24660) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24660 : ℝ)^2 / (mW 12330 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2098491/1000000000000))/2) * ((1-firstRatio 24660) * √(1-firstRatio 24660) *
      sixthConstant (e1CovarianceRatio 24660 (mW 12330) (1/10^6) rowEps))) /
    (712/10000 - 24660*(1+1/10^6)*((2098491/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24660 (mW 12330) /
    ((1/10^5) * ((mW 12330 : ℝ)*24660*((mW 12330 : ℝ)+24660+1)))^2 +
  8*(mW 12330 : ℝ)*24660*(24660+2)*(24660+3) /
    ((1/1000)*((mW 12330 : ℝ)*24660*(24660+2)))^2 +
  covarianceVarianceBound 24660 (mW 12330) /
    ((1/1000)*covarianceMeanBound 24660 (mW 12330))^2 +
  normVarianceBound 24660 (mW 12330) / (3*inputVarianceMean 24660 (mW 12330))^2

end BstLean.Part260.Row12330
#eval (do IO.println s!"P260 END 12330 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12331 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12331
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12331 = 208206384225556 := by
  have hu : mW 12331 ≤ 208206384225556 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12331 ≤ 208206384225555 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12331)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24662 ^ 2)
    ((25000000000000000000/3873897901141574042357357))
    ((25000000000000000000/3873740821508894552683103)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24662) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24662 : ℝ)^2 / (mW 12331 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2098319/1000000000000))/2) * ((1-firstRatio 24662) * √(1-firstRatio 24662) *
      sixthConstant (e1CovarianceRatio 24662 (mW 12331) (1/10^6) rowEps))) /
    (712/10000 - 24662*(1+1/10^6)*((2098319/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24662 (mW 12331) /
    ((1/10^5) * ((mW 12331 : ℝ)*24662*((mW 12331 : ℝ)+24662+1)))^2 +
  8*(mW 12331 : ℝ)*24662*(24662+2)*(24662+3) /
    ((1/1000)*((mW 12331 : ℝ)*24662*(24662+2)))^2 +
  covarianceVarianceBound 24662 (mW 12331) /
    ((1/1000)*covarianceMeanBound 24662 (mW 12331))^2 +
  normVarianceBound 24662 (mW 12331) / (3*inputVarianceMean 24662 (mW 12331))^2

end BstLean.Part260.Row12331
#eval (do IO.println s!"P260 END 12331 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12332 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12332
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12332 = 208265486992465 := by
  have hu : mW 12332 ≤ 208265486992465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12332 ≤ 208265486992464 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12332)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24664 ^ 2)
    ((6250000000000000000/968553015101733255420301))
    ((25000000000000000000/3874054980774253532006949)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24664) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24664 : ℝ)^2 / (mW 12332 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2098147/1000000000000))/2) * ((1-firstRatio 24664) * √(1-firstRatio 24664) *
      sixthConstant (e1CovarianceRatio 24664 (mW 12332) (1/10^6) rowEps))) /
    (712/10000 - 24664*(1+1/10^6)*((2098147/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24664 (mW 12332) /
    ((1/10^5) * ((mW 12332 : ℝ)*24664*((mW 12332 : ℝ)+24664+1)))^2 +
  8*(mW 12332 : ℝ)*24664*(24664+2)*(24664+3) /
    ((1/1000)*((mW 12332 : ℝ)*24664*(24664+2)))^2 +
  covarianceVarianceBound 24664 (mW 12332) /
    ((1/1000)*covarianceMeanBound 24664 (mW 12332))^2 +
  normVarianceBound 24664 (mW 12332) / (3*inputVarianceMean 24664 (mW 12332))^2

end BstLean.Part260.Row12332
#eval (do IO.println s!"P260 END 12332 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12333 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12333
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12333 = 208324601742175 := by
  have hu : mW 12333 ≤ 208324601742175 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12333 ≤ 208324601742174 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12333)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24666 ^ 2)
    ((25000000000000000000/3874526219672292001005051))
    ((5000000000000000000/774873828007922502266159)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24666) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24666 : ℝ)^2 / (mW 12333 : ℝ)) * (1 + 1/10^6)^2 *
    √(((83919/40000000000))/2) * ((1-firstRatio 24666) * √(1-firstRatio 24666) *
      sixthConstant (e1CovarianceRatio 24666 (mW 12333) (1/10^6) rowEps))) /
    (712/10000 - 24666*(1+1/10^6)*((83919/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24666 (mW 12333) /
    ((1/10^5) * ((mW 12333 : ℝ)*24666*((mW 12333 : ℝ)+24666+1)))^2 +
  8*(mW 12333 : ℝ)*24666*(24666+2)*(24666+3) /
    ((1/1000)*((mW 12333 : ℝ)*24666*(24666+2)))^2 +
  covarianceVarianceBound 24666 (mW 12333) /
    ((1/1000)*covarianceMeanBound 24666 (mW 12333))^2 +
  normVarianceBound 24666 (mW 12333) / (3*inputVarianceMean 24666 (mW 12333))^2

end BstLean.Part260.Row12333
#eval (do IO.println s!"P260 END 12333 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12334 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12334
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12334 = 208383728476142 := by
  have hu : mW 12334 ≤ 208383728476142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12334 ≤ 208383728476141 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12334)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24668 ^ 2)
    ((12500000000000000000/1937420189468825490164449))
    ((25000000000000000000/3874683299304971490654641)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24668) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24668 : ℝ)^2 / (mW 12334 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2097803/1000000000000))/2) * ((1-firstRatio 24668) * √(1-firstRatio 24668) *
      sixthConstant (e1CovarianceRatio 24668 (mW 12334) (1/10^6) rowEps))) /
    (712/10000 - 24668*(1+1/10^6)*((2097803/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24668 (mW 12334) /
    ((1/10^5) * ((mW 12334 : ℝ)*24668*((mW 12334 : ℝ)+24668+1)))^2 +
  8*(mW 12334 : ℝ)*24668*(24668+2)*(24668+3) /
    ((1/1000)*((mW 12334 : ℝ)*24668*(24668+2)))^2 +
  covarianceVarianceBound 24668 (mW 12334) /
    ((1/1000)*covarianceMeanBound 24668 (mW 12334))^2 +
  normVarianceBound 24668 (mW 12334) / (3*inputVarianceMean 24668 (mW 12334))^2

end BstLean.Part260.Row12334
#eval (do IO.println s!"P260 END 12334 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12335 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12335
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12335 = 208442867195825 := by
  have hu : mW 12335 ≤ 208442867195825 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12335 ≤ 208442867195824 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12335)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24670 ^ 2)
    ((5000000000000000000/775030907640601991930549))
    ((25000000000000000000/3874997458570330469978487)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24670) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24670 : ℝ)^2 / (mW 12335 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2097631/1000000000000))/2) * ((1-firstRatio 24670) * √(1-firstRatio 24670) *
      sixthConstant (e1CovarianceRatio 24670 (mW 12335) (1/10^6) rowEps))) /
    (712/10000 - 24670*(1+1/10^6)*((2097631/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24670 (mW 12335) /
    ((1/10^5) * ((mW 12335 : ℝ)*24670*((mW 12335 : ℝ)+24670+1)))^2 +
  8*(mW 12335 : ℝ)*24670*(24670+2)*(24670+3) /
    ((1/1000)*((mW 12335 : ℝ)*24670*(24670+2)))^2 +
  covarianceVarianceBound 24670 (mW 12335) /
    ((1/1000)*covarianceMeanBound 24670 (mW 12335))^2 +
  normVarianceBound 24670 (mW 12335) / (3*inputVarianceMean 24670 (mW 12335))^2

end BstLean.Part260.Row12335
#eval (do IO.println s!"P260 END 12335 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12336 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12336
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12336 = 208502017902682 := by
  have hu : mW 12336 ≤ 208502017902682 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12336 ≤ 208502017902681 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12336)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24672 ^ 2)
    ((1562500000000000000/242216793591773058686037))
    ((25000000000000000000/3875311617835689449302333)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24672) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24672 : ℝ)^2 / (mW 12336 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2097459/1000000000000))/2) * ((1-firstRatio 24672) * √(1-firstRatio 24672) *
      sixthConstant (e1CovarianceRatio 24672 (mW 12336) (1/10^6) rowEps))) /
    (712/10000 - 24672*(1+1/10^6)*((2097459/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24672 (mW 12336) /
    ((1/10^5) * ((mW 12336 : ℝ)*24672*((mW 12336 : ℝ)+24672+1)))^2 +
  8*(mW 12336 : ℝ)*24672*(24672+2)*(24672+3) /
    ((1/1000)*((mW 12336 : ℝ)*24672*(24672+2)))^2 +
  covarianceVarianceBound 24672 (mW 12336) /
    ((1/1000)*covarianceMeanBound 24672 (mW 12336))^2 +
  normVarianceBound 24672 (mW 12336) / (3*inputVarianceMean 24672 (mW 12336))^2

end BstLean.Part260.Row12336
#eval (do IO.println s!"P260 END 12336 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12337 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12337
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12337 = 208561180598169 := by
  have hu : mW 12337 ≤ 208561180598169 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12337 ≤ 208561180598168 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12337)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24674 ^ 2)
    ((25000000000000000000/3875782856733727918300439))
    ((25000000000000000000/3875625777101048428626179)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24674) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24674 : ℝ)^2 / (mW 12337 : ℝ)) * (1 + 1/10^6)^2 *
    √(((262161/125000000000))/2) * ((1-firstRatio 24674) * √(1-firstRatio 24674) *
      sixthConstant (e1CovarianceRatio 24674 (mW 12337) (1/10^6) rowEps))) /
    (712/10000 - 24674*(1+1/10^6)*((262161/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24674 (mW 12337) /
    ((1/10^5) * ((mW 12337 : ℝ)*24674*((mW 12337 : ℝ)+24674+1)))^2 +
  8*(mW 12337 : ℝ)*24674*(24674+2)*(24674+3) /
    ((1/1000)*((mW 12337 : ℝ)*24674*(24674+2)))^2 +
  covarianceVarianceBound 24674 (mW 12337) /
    ((1/1000)*covarianceMeanBound 24674 (mW 12337))^2 +
  normVarianceBound 24674 (mW 12337) / (3*inputVarianceMean 24674 (mW 12337))^2

end BstLean.Part260.Row12337
#eval (do IO.println s!"P260 END 12337 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12338 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12338
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12338 = 208620355283745 := by
  have hu : mW 12338 ≤ 208620355283745 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12338 ≤ 208620355283744 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12338)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24676 ^ 2)
    ((12500000000000000000/1938048507999543448812143))
    ((1000000000000000000/155037597454656296318001)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24676) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24676 : ℝ)^2 / (mW 12338 : ℝ)) * (1 + 1/10^6)^2 *
    √(((524279/250000000000))/2) * ((1-firstRatio 24676) * √(1-firstRatio 24676) *
      sixthConstant (e1CovarianceRatio 24676 (mW 12338) (1/10^6) rowEps))) /
    (712/10000 - 24676*(1+1/10^6)*((524279/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24676 (mW 12338) /
    ((1/10^5) * ((mW 12338 : ℝ)*24676*((mW 12338 : ℝ)+24676+1)))^2 +
  8*(mW 12338 : ℝ)*24676*(24676+2)*(24676+3) /
    ((1/1000)*((mW 12338 : ℝ)*24676*(24676+2)))^2 +
  covarianceVarianceBound 24676 (mW 12338) /
    ((1/1000)*covarianceMeanBound 24676 (mW 12338))^2 +
  normVarianceBound 24676 (mW 12338) / (3*inputVarianceMean 24676 (mW 12338))^2

end BstLean.Part260.Row12338
#eval (do IO.println s!"P260 END 12338 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12339 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12339
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12339 = 208679541960868 := by
  have hu : mW 12339 ≤ 208679541960868 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12339 ≤ 208679541960867 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12339)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24678 ^ 2)
    ((25000000000000000000/3876411175264445876948133))
    ((25000000000000000000/3876254095631766387273871)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24678) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24678 : ℝ)^2 / (mW 12339 : ℝ)) * (1 + 1/10^6)^2 *
    √(((131059/62500000000))/2) * ((1-firstRatio 24678) * √(1-firstRatio 24678) *
      sixthConstant (e1CovarianceRatio 24678 (mW 12339) (1/10^6) rowEps))) /
    (712/10000 - 24678*(1+1/10^6)*((131059/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24678 (mW 12339) /
    ((1/10^5) * ((mW 12339 : ℝ)*24678*((mW 12339 : ℝ)+24678+1)))^2 +
  8*(mW 12339 : ℝ)*24678*(24678+2)*(24678+3) /
    ((1/1000)*((mW 12339 : ℝ)*24678*(24678+2)))^2 +
  covarianceVarianceBound 24678 (mW 12339) /
    ((1/1000)*covarianceMeanBound 24678 (mW 12339))^2 +
  normVarianceBound 24678 (mW 12339) / (3*inputVarianceMean 24678 (mW 12339))^2

end BstLean.Part260.Row12339
#eval (do IO.println s!"P260 END 12339 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12340 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12340
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12340 = 208738740630996 := by
  have hu : mW 12340 ≤ 208738740630996 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12340 ≤ 208738740630995 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12340)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24680 ^ 2)
    ((1250000000000000000/193836266726490242813599))
    ((25000000000000000000/3876568254897125366597717)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24680) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24680 : ℝ)^2 / (mW 12340 : ℝ)) * (1 + 1/10^6)^2 *
    √(((524193/250000000000))/2) * ((1-firstRatio 24680) * √(1-firstRatio 24680) *
      sixthConstant (e1CovarianceRatio 24680 (mW 12340) (1/10^6) rowEps))) /
    (712/10000 - 24680*(1+1/10^6)*((524193/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24680 (mW 12340) /
    ((1/10^5) * ((mW 12340 : ℝ)*24680*((mW 12340 : ℝ)+24680+1)))^2 +
  8*(mW 12340 : ℝ)*24680*(24680+2)*(24680+3) /
    ((1/1000)*((mW 12340 : ℝ)*24680*(24680+2)))^2 +
  covarianceVarianceBound 24680 (mW 12340) /
    ((1/1000)*covarianceMeanBound 24680 (mW 12340))^2 +
  normVarianceBound 24680 (mW 12340) / (3*inputVarianceMean 24680 (mW 12340))^2

end BstLean.Part260.Row12340
#eval (do IO.println s!"P260 END 12340 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12341 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12341
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12341 = 208797951295586 := by
  have hu : mW 12341 ≤ 208797951295586 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12341 ≤ 208797951295585 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12341)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24682 ^ 2)
    ((25000000000000000000/3877039493795163835595827))
    ((25000000000000000000/3876882414162484345921563)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24682) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24682 : ℝ)^2 / (mW 12341 : ℝ)) * (1 + 1/10^6)^2 *
    √(((10483/5000000000))/2) * ((1-firstRatio 24682) * √(1-firstRatio 24682) *
      sixthConstant (e1CovarianceRatio 24682 (mW 12341) (1/10^6) rowEps))) /
    (712/10000 - 24682*(1+1/10^6)*((10483/5000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24682 (mW 12341) /
    ((1/10^5) * ((mW 12341 : ℝ)*24682*((mW 12341 : ℝ)+24682+1)))^2 +
  8*(mW 12341 : ℝ)*24682*(24682+2)*(24682+3) /
    ((1/1000)*((mW 12341 : ℝ)*24682*(24682+2)))^2 +
  covarianceVarianceBound 24682 (mW 12341) /
    ((1/1000)*covarianceMeanBound 24682 (mW 12341))^2 +
  normVarianceBound 24682 (mW 12341) / (3*inputVarianceMean 24682 (mW 12341))^2

end BstLean.Part260.Row12341
#eval (do IO.println s!"P260 END 12341 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12342 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12342
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12342 = 208857173956096 := by
  have hu : mW 12342 ≤ 208857173956096 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12342 ≤ 208857173956095 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12342)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24684 ^ 2)
    ((12500000000000000000/1938676826530261407459837))
    ((25000000000000000000/3877196573427843325245409)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24684) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24684 : ℝ)^2 / (mW 12342 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2096429/1000000000000))/2) * ((1-firstRatio 24684) * √(1-firstRatio 24684) *
      sixthConstant (e1CovarianceRatio 24684 (mW 12342) (1/10^6) rowEps))) /
    (712/10000 - 24684*(1+1/10^6)*((2096429/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24684 (mW 12342) /
    ((1/10^5) * ((mW 12342 : ℝ)*24684*((mW 12342 : ℝ)+24684+1)))^2 +
  8*(mW 12342 : ℝ)*24684*(24684+2)*(24684+3) /
    ((1/1000)*((mW 12342 : ℝ)*24684*(24684+2)))^2 +
  covarianceVarianceBound 24684 (mW 12342) /
    ((1/1000)*covarianceMeanBound 24684 (mW 12342))^2 +
  normVarianceBound 24684 (mW 12342) / (3*inputVarianceMean 24684 (mW 12342))^2

end BstLean.Part260.Row12342
#eval (do IO.println s!"P260 END 12342 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12343 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12343
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12343 = 208916408613985 := by
  have hu : mW 12343 ≤ 208916408613985 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12343 ≤ 208916408613984 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12343)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24686 ^ 2)
    ((25000000000000000000/3877667812325881794243521))
    ((5000000000000000000/775502146538640460913851)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24686) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24686 : ℝ)^2 / (mW 12343 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2096257/1000000000000))/2) * ((1-firstRatio 24686) * √(1-firstRatio 24686) *
      sixthConstant (e1CovarianceRatio 24686 (mW 12343) (1/10^6) rowEps))) /
    (712/10000 - 24686*(1+1/10^6)*((2096257/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24686 (mW 12343) /
    ((1/10^5) * ((mW 12343 : ℝ)*24686*((mW 12343 : ℝ)+24686+1)))^2 +
  8*(mW 12343 : ℝ)*24686*(24686+2)*(24686+3) /
    ((1/1000)*((mW 12343 : ℝ)*24686*(24686+2)))^2 +
  covarianceVarianceBound 24686 (mW 12343) /
    ((1/1000)*covarianceMeanBound 24686 (mW 12343))^2 +
  normVarianceBound 24686 (mW 12343) / (3*inputVarianceMean 24686 (mW 12343))^2

end BstLean.Part260.Row12343
#eval (do IO.println s!"P260 END 12343 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12344 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12344
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12344 = 208975655270712 := by
  have hu : mW 12344 ≤ 208975655270712 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12344 ≤ 208975655270711 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12344)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24688 ^ 2)
    ((3125000000000000000/484747746448905096695921))
    ((25000000000000000000/3877824891958561283893101)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24688) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24688 : ℝ)^2 / (mW 12344 : ℝ)) * (1 + 1/10^6)^2 *
    √(((419217/200000000000))/2) * ((1-firstRatio 24688) * √(1-firstRatio 24688) *
      sixthConstant (e1CovarianceRatio 24688 (mW 12344) (1/10^6) rowEps))) /
    (712/10000 - 24688*(1+1/10^6)*((419217/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24688 (mW 12344) /
    ((1/10^5) * ((mW 12344 : ℝ)*24688*((mW 12344 : ℝ)+24688+1)))^2 +
  8*(mW 12344 : ℝ)*24688*(24688+2)*(24688+3) /
    ((1/1000)*((mW 12344 : ℝ)*24688*(24688+2)))^2 +
  covarianceVarianceBound 24688 (mW 12344) /
    ((1/1000)*covarianceMeanBound 24688 (mW 12344))^2 +
  normVarianceBound 24688 (mW 12344) / (3*inputVarianceMean 24688 (mW 12344))^2

end BstLean.Part260.Row12344
#eval (do IO.println s!"P260 END 12344 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12345 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12345
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12345 = 209034913927733 := by
  have hu : mW 12345 ≤ 209034913927733 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12345 ≤ 209034913927732 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12345)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24690 ^ 2)
    ((5000000000000000000/775659226171319950578243))
    ((25000000000000000000/3878139051223920263216947)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24690) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24690 : ℝ)^2 / (mW 12345 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1047957/500000000000))/2) * ((1-firstRatio 24690) * √(1-firstRatio 24690) *
      sixthConstant (e1CovarianceRatio 24690 (mW 12345) (1/10^6) rowEps))) /
    (712/10000 - 24690*(1+1/10^6)*((1047957/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24690 (mW 12345) /
    ((1/10^5) * ((mW 12345 : ℝ)*24690*((mW 12345 : ℝ)+24690+1)))^2 +
  8*(mW 12345 : ℝ)*24690*(24690+2)*(24690+3) /
    ((1/1000)*((mW 12345 : ℝ)*24690*(24690+2)))^2 +
  covarianceVarianceBound 24690 (mW 12345) /
    ((1/1000)*covarianceMeanBound 24690 (mW 12345))^2 +
  normVarianceBound 24690 (mW 12345) / (3*inputVarianceMean 24690 (mW 12345))^2

end BstLean.Part260.Row12345
#eval (do IO.println s!"P260 END 12345 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12346 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12346
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12346 = 209094184586507 := by
  have hu : mW 12346 ≤ 209094184586507 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12346 ≤ 209094184586506 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12346)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24692 ^ 2)
    ((12500000000000000000/1939305145060979366107531))
    ((25000000000000000000/3878453210489279242540793)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24692) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24692 : ℝ)^2 / (mW 12346 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1047871/500000000000))/2) * ((1-firstRatio 24692) * √(1-firstRatio 24692) *
      sixthConstant (e1CovarianceRatio 24692 (mW 12346) (1/10^6) rowEps))) /
    (712/10000 - 24692*(1+1/10^6)*((1047871/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24692 (mW 12346) /
    ((1/10^5) * ((mW 12346 : ℝ)*24692*((mW 12346 : ℝ)+24692+1)))^2 +
  8*(mW 12346 : ℝ)*24692*(24692+2)*(24692+3) /
    ((1/1000)*((mW 12346 : ℝ)*24692*(24692+2)))^2 +
  covarianceVarianceBound 24692 (mW 12346) /
    ((1/1000)*covarianceMeanBound 24692 (mW 12346))^2 +
  normVarianceBound 24692 (mW 12346) / (3*inputVarianceMean 24692 (mW 12346))^2

end BstLean.Part260.Row12346
#eval (do IO.println s!"P260 END 12346 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12347 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12347
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12347 = 209153467248493 := by
  have hu : mW 12347 ≤ 209153467248493 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12347 ≤ 209153467248492 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12347)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24694 ^ 2)
    ((25000000000000000000/3878924449387317711538909))
    ((25000000000000000000/3878767369754638221864639)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24694) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24694 : ℝ)^2 / (mW 12347 : ℝ)) * (1 + 1/10^6)^2 *
    √(((209557/100000000000))/2) * ((1-firstRatio 24694) * √(1-firstRatio 24694) *
      sixthConstant (e1CovarianceRatio 24694 (mW 12347) (1/10^6) rowEps))) /
    (712/10000 - 24694*(1+1/10^6)*((209557/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24694 (mW 12347) /
    ((1/10^5) * ((mW 12347 : ℝ)*24694*((mW 12347 : ℝ)+24694+1)))^2 +
  8*(mW 12347 : ℝ)*24694*(24694+2)*(24694+3) /
    ((1/1000)*((mW 12347 : ℝ)*24694*(24694+2)))^2 +
  covarianceVarianceBound 24694 (mW 12347) /
    ((1/1000)*covarianceMeanBound 24694 (mW 12347))^2 +
  normVarianceBound 24694 (mW 12347) / (3*inputVarianceMean 24694 (mW 12347))^2

end BstLean.Part260.Row12347
#eval (do IO.println s!"P260 END 12347 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12348 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12348
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12348 = 209212761915149 := by
  have hu : mW 12348 ≤ 209212761915149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12348 ≤ 209212761915148 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12348)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24696 ^ 2)
    ((6250000000000000000/969809652163169172715689))
    ((5000000000000000000/775816305803999440237697)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24696) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24696 : ℝ)^2 / (mW 12348 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2095399/1000000000000))/2) * ((1-firstRatio 24696) * √(1-firstRatio 24696) *
      sixthConstant (e1CovarianceRatio 24696 (mW 12348) (1/10^6) rowEps))) /
    (712/10000 - 24696*(1+1/10^6)*((2095399/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24696 (mW 12348) /
    ((1/10^5) * ((mW 12348 : ℝ)*24696*((mW 12348 : ℝ)+24696+1)))^2 +
  8*(mW 12348 : ℝ)*24696*(24696+2)*(24696+3) /
    ((1/1000)*((mW 12348 : ℝ)*24696*(24696+2)))^2 +
  covarianceVarianceBound 24696 (mW 12348) /
    ((1/1000)*covarianceMeanBound 24696 (mW 12348))^2 +
  normVarianceBound 24696 (mW 12348) / (3*inputVarianceMean 24696 (mW 12348))^2

end BstLean.Part260.Row12348
#eval (do IO.println s!"P260 END 12348 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12349 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12349
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12349 = 209272068587933 := by
  have hu : mW 12349 ≤ 209272068587933 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12349 ≤ 209272068587932 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12349)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24698 ^ 2)
    ((25000000000000000000/3879552767918035670186603))
    ((25000000000000000000/3879395688285356180512331)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24698) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24698 : ℝ)^2 / (mW 12349 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2095227/1000000000000))/2) * ((1-firstRatio 24698) * √(1-firstRatio 24698) *
      sixthConstant (e1CovarianceRatio 24698 (mW 12349) (1/10^6) rowEps))) /
    (712/10000 - 24698*(1+1/10^6)*((2095227/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24698 (mW 12349) /
    ((1/10^5) * ((mW 12349 : ℝ)*24698*((mW 12349 : ℝ)+24698+1)))^2 +
  8*(mW 12349 : ℝ)*24698*(24698+2)*(24698+3) /
    ((1/1000)*((mW 12349 : ℝ)*24698*(24698+2)))^2 +
  covarianceVarianceBound 24698 (mW 12349) /
    ((1/1000)*covarianceMeanBound 24698 (mW 12349))^2 +
  normVarianceBound 24698 (mW 12349) / (3*inputVarianceMean 24698 (mW 12349))^2

end BstLean.Part260.Row12349
#eval (do IO.println s!"P260 END 12349 0 {← IO.monoMsNow}" : IO Unit)
