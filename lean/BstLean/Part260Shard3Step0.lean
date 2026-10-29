import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part259Data15
import BstLean.Part259Data16
import BstLean.Part259Data17
import BstLean.Part259Data18
import BstLean.Part259Data19
#eval (do IO.println s!"P260 START 12300 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12300
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12300 = 206380133970726 := by
  have hu : mW 12300 ≤ 206380133970726 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12300 ≤ 206380133970725 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12300)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24600 ^ 2)
    ((250000000000000000/38641589639154456833181))
    ((25000000000000000000/3864001884282766193643877)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24600) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24600 : ℝ)^2 / (mW 12300 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1051833/500000000000))/2) * ((1-firstRatio 24600) * √(1-firstRatio 24600) *
      sixthConstant (e1CovarianceRatio 24600 (mW 12300) (1/10^6) rowEps))) /
    (712/10000 - 24600*(1+1/10^6)*((1051833/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24600 (mW 12300) /
    ((1/10^5) * ((mW 12300 : ℝ)*24600*((mW 12300 : ℝ)+24600+1)))^2 +
  8*(mW 12300 : ℝ)*24600*(24600+2)*(24600+3) /
    ((1/1000)*((mW 12300 : ℝ)*24600*(24600+2)))^2 +
  covarianceVarianceBound 24600 (mW 12300) /
    ((1/1000)*covarianceMeanBound 24600 (mW 12300))^2 +
  normVarianceBound 24600 (mW 12300) / (3*inputVarianceMean 24600 (mW 12300))^2

end BstLean.Part260.Row12300
#eval (do IO.println s!"P260 END 12300 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12301 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12301
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12301 = 206438865993446 := by
  have hu : mW 12301 ≤ 206438865993446 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12301 ≤ 206438865993445 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12301)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24602 ^ 2)
    ((25000000000000000000/3864473123180804662641947))
    ((25000000000000000000/3864316043548125172967723)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24602) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24602 : ℝ)^2 / (mW 12301 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2103493/1000000000000))/2) * ((1-firstRatio 24602) * √(1-firstRatio 24602) *
      sixthConstant (e1CovarianceRatio 24602 (mW 12301) (1/10^6) rowEps))) /
    (712/10000 - 24602*(1+1/10^6)*((2103493/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24602 (mW 12301) /
    ((1/10^5) * ((mW 12301 : ℝ)*24602*((mW 12301 : ℝ)+24602+1)))^2 +
  8*(mW 12301 : ℝ)*24602*(24602+2)*(24602+3) /
    ((1/1000)*((mW 12301 : ℝ)*24602*(24602+2)))^2 +
  covarianceVarianceBound 24602 (mW 12301) /
    ((1/1000)*covarianceMeanBound 24602 (mW 12301))^2 +
  normVarianceBound 24602 (mW 12301) / (3*inputVarianceMean 24602 (mW 12301))^2

end BstLean.Part260.Row12301
#eval (do IO.println s!"P260 END 12301 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12302 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12302
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12302 = 206497609953811 := by
  have hu : mW 12302 ≤ 206497609953811 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12302 ≤ 206497609953810 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12302)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24604 ^ 2)
    ((12500000000000000000/1932393641223081820982897))
    ((25000000000000000000/3864630202813484152291569)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24604) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24604 : ℝ)^2 / (mW 12302 : ℝ)) * (1 + 1/10^6)^2 *
    √(((52583/25000000000))/2) * ((1-firstRatio 24604) * √(1-firstRatio 24604) *
      sixthConstant (e1CovarianceRatio 24604 (mW 12302) (1/10^6) rowEps))) /
    (712/10000 - 24604*(1+1/10^6)*((52583/25000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24604 (mW 12302) /
    ((1/10^5) * ((mW 12302 : ℝ)*24604*((mW 12302 : ℝ)+24604+1)))^2 +
  8*(mW 12302 : ℝ)*24604*(24604+2)*(24604+3) /
    ((1/1000)*((mW 12302 : ℝ)*24604*(24604+2)))^2 +
  covarianceVarianceBound 24604 (mW 12302) /
    ((1/1000)*covarianceMeanBound 24604 (mW 12302))^2 +
  normVarianceBound 24604 (mW 12302) / (3*inputVarianceMean 24604 (mW 12302))^2

end BstLean.Part260.Row12302
#eval (do IO.println s!"P260 END 12302 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12303 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12303
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12303 = 206556365853277 := by
  have hu : mW 12303 ≤ 206556365853277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12303 ≤ 206556365853276 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12303)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24606 ^ 2)
    ((25000000000000000000/3865101441711522621289641))
    ((5000000000000000000/772988872415768626323083)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24606) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24606 : ℝ)^2 / (mW 12303 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2103147/1000000000000))/2) * ((1-firstRatio 24606) * √(1-firstRatio 24606) *
      sixthConstant (e1CovarianceRatio 24606 (mW 12303) (1/10^6) rowEps))) /
    (712/10000 - 24606*(1+1/10^6)*((2103147/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24606 (mW 12303) /
    ((1/10^5) * ((mW 12303 : ℝ)*24606*((mW 12303 : ℝ)+24606+1)))^2 +
  8*(mW 12303 : ℝ)*24606*(24606+2)*(24606+3) /
    ((1/1000)*((mW 12303 : ℝ)*24606*(24606+2)))^2 +
  covarianceVarianceBound 24606 (mW 12303) /
    ((1/1000)*covarianceMeanBound 24606 (mW 12303))^2 +
  normVarianceBound 24606 (mW 12303) / (3*inputVarianceMean 24606 (mW 12303))^2

end BstLean.Part260.Row12303
#eval (do IO.println s!"P260 END 12303 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12304 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12304
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12304 = 206615133693301 := by
  have hu : mW 12304 ≤ 206615133693301 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12304 ≤ 206615133693300 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12304)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24608 ^ 2)
    ((1562500000000000000/241588475061055100038343))
    ((25000000000000000000/3865258521344202110939261)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24608) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24608 : ℝ)^2 / (mW 12304 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1051487/500000000000))/2) * ((1-firstRatio 24608) * √(1-firstRatio 24608) *
      sixthConstant (e1CovarianceRatio 24608 (mW 12304) (1/10^6) rowEps))) /
    (712/10000 - 24608*(1+1/10^6)*((1051487/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24608 (mW 12304) /
    ((1/10^5) * ((mW 12304 : ℝ)*24608*((mW 12304 : ℝ)+24608+1)))^2 +
  8*(mW 12304 : ℝ)*24608*(24608+2)*(24608+3) /
    ((1/1000)*((mW 12304 : ℝ)*24608*(24608+2)))^2 +
  covarianceVarianceBound 24608 (mW 12304) /
    ((1/1000)*covarianceMeanBound 24608 (mW 12304))^2 +
  normVarianceBound 24608 (mW 12304) / (3*inputVarianceMean 24608 (mW 12304))^2

end BstLean.Part260.Row12304
#eval (do IO.println s!"P260 END 12304 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12305 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12305
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12305 = 206673913475337 := by
  have hu : mW 12305 ≤ 206673913475337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12305 ≤ 206673913475336 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12305)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24610 ^ 2)
    ((5000000000000000000/773145952048448115987467))
    ((25000000000000000000/3865572680609561090263107)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24610) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24610 : ℝ)^2 / (mW 12305 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2102801/1000000000000))/2) * ((1-firstRatio 24610) * √(1-firstRatio 24610) *
      sixthConstant (e1CovarianceRatio 24610 (mW 12305) (1/10^6) rowEps))) /
    (712/10000 - 24610*(1+1/10^6)*((2102801/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24610 (mW 12305) /
    ((1/10^5) * ((mW 12305 : ℝ)*24610*((mW 12305 : ℝ)+24610+1)))^2 +
  8*(mW 12305 : ℝ)*24610*(24610+2)*(24610+3) /
    ((1/1000)*((mW 12305 : ℝ)*24610*(24610+2)))^2 +
  covarianceVarianceBound 24610 (mW 12305) /
    ((1/1000)*covarianceMeanBound 24610 (mW 12305))^2 +
  normVarianceBound 24610 (mW 12305) / (3*inputVarianceMean 24610 (mW 12305))^2

end BstLean.Part260.Row12305
#eval (do IO.println s!"P260 END 12305 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12306 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12306
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12306 = 206732705200842 := by
  have hu : mW 12306 ≤ 206732705200842 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12306 ≤ 206732705200841 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12306)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24612 ^ 2)
    ((12500000000000000000/1933021959753799779630591))
    ((25000000000000000000/3865886839874920069586953)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24612) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24612 : ℝ)^2 / (mW 12306 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2102629/1000000000000))/2) * ((1-firstRatio 24612) * √(1-firstRatio 24612) *
      sixthConstant (e1CovarianceRatio 24612 (mW 12306) (1/10^6) rowEps))) /
    (712/10000 - 24612*(1+1/10^6)*((2102629/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24612 (mW 12306) /
    ((1/10^5) * ((mW 12306 : ℝ)*24612*((mW 12306 : ℝ)+24612+1)))^2 +
  8*(mW 12306 : ℝ)*24612*(24612+2)*(24612+3) /
    ((1/1000)*((mW 12306 : ℝ)*24612*(24612+2)))^2 +
  covarianceVarianceBound 24612 (mW 12306) /
    ((1/1000)*covarianceMeanBound 24612 (mW 12306))^2 +
  normVarianceBound 24612 (mW 12306) / (3*inputVarianceMean 24612 (mW 12306))^2

end BstLean.Part260.Row12306
#eval (do IO.println s!"P260 END 12306 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12307 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12307
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12307 = 206791508871272 := by
  have hu : mW 12307 ≤ 206791508871272 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12307 ≤ 206791508871271 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12307)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24614 ^ 2)
    ((25000000000000000000/3866358078772958538585029))
    ((25000000000000000000/3866200999140279048910799)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24614) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24614 : ℝ)^2 / (mW 12307 : ℝ)) * (1 + 1/10^6)^2 *
    √(((262807/125000000000))/2) * ((1-firstRatio 24614) * √(1-firstRatio 24614) *
      sixthConstant (e1CovarianceRatio 24614 (mW 12307) (1/10^6) rowEps))) /
    (712/10000 - 24614*(1+1/10^6)*((262807/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24614 (mW 12307) /
    ((1/10^5) * ((mW 12307 : ℝ)*24614*((mW 12307 : ℝ)+24614+1)))^2 +
  8*(mW 12307 : ℝ)*24614*(24614+2)*(24614+3) /
    ((1/1000)*((mW 12307 : ℝ)*24614*(24614+2)))^2 +
  covarianceVarianceBound 24614 (mW 12307) /
    ((1/1000)*covarianceMeanBound 24614 (mW 12307))^2 +
  normVarianceBound 24614 (mW 12307) / (3*inputVarianceMean 24614 (mW 12307))^2

end BstLean.Part260.Row12307
#eval (do IO.println s!"P260 END 12307 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12308 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12308
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12308 = 206850324488083 := by
  have hu : mW 12308 ≤ 206850324488083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12308 ≤ 206850324488082 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12308)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24616 ^ 2)
    ((6250000000000000000/966668059509579379477219))
    ((5000000000000000000/773303031681127605646929)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24616) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24616 : ℝ)^2 / (mW 12308 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2102283/1000000000000))/2) * ((1-firstRatio 24616) * √(1-firstRatio 24616) *
      sixthConstant (e1CovarianceRatio 24616 (mW 12308) (1/10^6) rowEps))) /
    (712/10000 - 24616*(1+1/10^6)*((2102283/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24616 (mW 12308) /
    ((1/10^5) * ((mW 12308 : ℝ)*24616*((mW 12308 : ℝ)+24616+1)))^2 +
  8*(mW 12308 : ℝ)*24616*(24616+2)*(24616+3) /
    ((1/1000)*((mW 12308 : ℝ)*24616*(24616+2)))^2 +
  covarianceVarianceBound 24616 (mW 12308) /
    ((1/1000)*covarianceMeanBound 24616 (mW 12308))^2 +
  normVarianceBound 24616 (mW 12308) / (3*inputVarianceMean 24616 (mW 12308))^2

end BstLean.Part260.Row12308
#eval (do IO.println s!"P260 END 12308 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12309 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12309
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12309 = 206909152052731 := by
  have hu : mW 12309 ≤ 206909152052731 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12309 ≤ 206909152052730 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12309)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24618 ^ 2)
    ((25000000000000000000/3866986397303676497232723))
    ((25000000000000000000/3866829317670997007558491)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24618) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24618 : ℝ)^2 / (mW 12309 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2102111/1000000000000))/2) * ((1-firstRatio 24618) * √(1-firstRatio 24618) *
      sixthConstant (e1CovarianceRatio 24618 (mW 12309) (1/10^6) rowEps))) /
    (712/10000 - 24618*(1+1/10^6)*((2102111/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24618 (mW 12309) /
    ((1/10^5) * ((mW 12309 : ℝ)*24618*((mW 12309 : ℝ)+24618+1)))^2 +
  8*(mW 12309 : ℝ)*24618*(24618+2)*(24618+3) /
    ((1/1000)*((mW 12309 : ℝ)*24618*(24618+2)))^2 +
  covarianceVarianceBound 24618 (mW 12309) /
    ((1/1000)*covarianceMeanBound 24618 (mW 12309))^2 +
  normVarianceBound 24618 (mW 12309) / (3*inputVarianceMean 24618 (mW 12309))^2

end BstLean.Part260.Row12309
#eval (do IO.println s!"P260 END 12309 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12310 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12310
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12310 = 206967991566671 := by
  have hu : mW 12310 ≤ 206967991566671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12310 ≤ 206967991566670 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12310)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24620 ^ 2)
    ((2500000000000000000/386730055656903547655657))
    ((25000000000000000000/3867143476936355986882337)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24620) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24620 : ℝ)^2 / (mW 12310 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1050969/500000000000))/2) * ((1-firstRatio 24620) * √(1-firstRatio 24620) *
      sixthConstant (e1CovarianceRatio 24620 (mW 12310) (1/10^6) rowEps))) /
    (712/10000 - 24620*(1+1/10^6)*((1050969/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24620 (mW 12310) /
    ((1/10^5) * ((mW 12310 : ℝ)*24620*((mW 12310 : ℝ)+24620+1)))^2 +
  8*(mW 12310 : ℝ)*24620*(24620+2)*(24620+3) /
    ((1/1000)*((mW 12310 : ℝ)*24620*(24620+2)))^2 +
  covarianceVarianceBound 24620 (mW 12310) /
    ((1/1000)*covarianceMeanBound 24620 (mW 12310))^2 +
  normVarianceBound 24620 (mW 12310) / (3*inputVarianceMean 24620 (mW 12310))^2

end BstLean.Part260.Row12310
#eval (do IO.println s!"P260 END 12310 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12311 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12311
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12311 = 207026843031361 := by
  have hu : mW 12311 ≤ 207026843031361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12311 ≤ 207026843031360 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12311)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24622 ^ 2)
    ((25000000000000000000/3867614715834394455880417))
    ((25000000000000000000/3867457636201714966206183)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24622) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24622 : ℝ)^2 / (mW 12311 : ℝ)) * (1 + 1/10^6)^2 *
    √(((420353/200000000000))/2) * ((1-firstRatio 24622) * √(1-firstRatio 24622) *
      sixthConstant (e1CovarianceRatio 24622 (mW 12311) (1/10^6) rowEps))) /
    (712/10000 - 24622*(1+1/10^6)*((420353/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24622 (mW 12311) /
    ((1/10^5) * ((mW 12311 : ℝ)*24622*((mW 12311 : ℝ)+24622+1)))^2 +
  8*(mW 12311 : ℝ)*24622*(24622+2)*(24622+3) /
    ((1/1000)*((mW 12311 : ℝ)*24622*(24622+2)))^2 +
  covarianceVarianceBound 24622 (mW 12311) /
    ((1/1000)*covarianceMeanBound 24622 (mW 12311))^2 +
  normVarianceBound 24622 (mW 12311) / (3*inputVarianceMean 24622 (mW 12311))^2

end BstLean.Part260.Row12311
#eval (do IO.println s!"P260 END 12311 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12312 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12312
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12312 = 207085706448256 := by
  have hu : mW 12312 ≤ 207085706448256 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12312 ≤ 207085706448255 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12312)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24624 ^ 2)
    ((3125000000000000000/483491109387469179400533))
    ((25000000000000000000/3867771795467073945530029)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24624) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24624 : ℝ)^2 / (mW 12312 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2101593/1000000000000))/2) * ((1-firstRatio 24624) * √(1-firstRatio 24624) *
      sixthConstant (e1CovarianceRatio 24624 (mW 12312) (1/10^6) rowEps))) /
    (712/10000 - 24624*(1+1/10^6)*((2101593/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24624 (mW 12312) /
    ((1/10^5) * ((mW 12312 : ℝ)*24624*((mW 12312 : ℝ)+24624+1)))^2 +
  8*(mW 12312 : ℝ)*24624*(24624+2)*(24624+3) /
    ((1/1000)*((mW 12312 : ℝ)*24624*(24624+2)))^2 +
  covarianceVarianceBound 24624 (mW 12312) /
    ((1/1000)*covarianceMeanBound 24624 (mW 12312))^2 +
  normVarianceBound 24624 (mW 12312) / (3*inputVarianceMean 24624 (mW 12312))^2

end BstLean.Part260.Row12312
#eval (do IO.println s!"P260 END 12312 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12313 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12313
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12313 = 207144581818814 := by
  have hu : mW 12313 ≤ 207144581818814 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12313 ≤ 207144581818813 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12313)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24626 ^ 2)
    ((25000000000000000000/3868243034365112414528111))
    ((200000000000000000/30944687637859463398831)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24626) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24626 : ℝ)^2 / (mW 12313 : ℝ)) * (1 + 1/10^6)^2 *
    √(((105071/50000000000))/2) * ((1-firstRatio 24626) * √(1-firstRatio 24626) *
      sixthConstant (e1CovarianceRatio 24626 (mW 12313) (1/10^6) rowEps))) /
    (712/10000 - 24626*(1+1/10^6)*((105071/50000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24626 (mW 12313) /
    ((1/10^5) * ((mW 12313 : ℝ)*24626*((mW 12313 : ℝ)+24626+1)))^2 +
  8*(mW 12313 : ℝ)*24626*(24626+2)*(24626+3) /
    ((1/1000)*((mW 12313 : ℝ)*24626*(24626+2)))^2 +
  covarianceVarianceBound 24626 (mW 12313) /
    ((1/1000)*covarianceMeanBound 24626 (mW 12313))^2 +
  normVarianceBound 24626 (mW 12313) / (3*inputVarianceMean 24626 (mW 12313))^2

end BstLean.Part260.Row12313
#eval (do IO.println s!"P260 END 12313 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12314 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12314
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12314 = 207203469144489 := by
  have hu : mW 12314 ≤ 207203469144489 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12314 ≤ 207203469144488 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12314)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24628 ^ 2)
    ((12500000000000000000/1934278596815235696925979))
    ((25000000000000000000/3868400113997791904177721)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24628) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24628 : ℝ)^2 / (mW 12314 : ℝ)) * (1 + 1/10^6)^2 *
    √(((513/244140625))/2) * ((1-firstRatio 24628) * √(1-firstRatio 24628) *
      sixthConstant (e1CovarianceRatio 24628 (mW 12314) (1/10^6) rowEps))) /
    (712/10000 - 24628*(1+1/10^6)*((513/244140625)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24628 (mW 12314) /
    ((1/10^5) * ((mW 12314 : ℝ)*24628*((mW 12314 : ℝ)+24628+1)))^2 +
  8*(mW 12314 : ℝ)*24628*(24628+2)*(24628+3) /
    ((1/1000)*((mW 12314 : ℝ)*24628*(24628+2)))^2 +
  covarianceVarianceBound 24628 (mW 12314) /
    ((1/1000)*covarianceMeanBound 24628 (mW 12314))^2 +
  normVarianceBound 24628 (mW 12314) / (3*inputVarianceMean 24628 (mW 12314))^2

end BstLean.Part260.Row12314
#eval (do IO.println s!"P260 END 12314 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12315 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12315
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12315 = 207262368426739 := by
  have hu : mW 12315 ≤ 207262368426739 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12315 ≤ 207262368426738 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12315)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24630 ^ 2)
    ((5000000000000000000/773774270579166074635161))
    ((25000000000000000000/3868714273263150883501567)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24630) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24630 : ℝ)^2 / (mW 12315 : ℝ)) * (1 + 1/10^6)^2 *
    √(((84043/40000000000))/2) * ((1-firstRatio 24630) * √(1-firstRatio 24630) *
      sixthConstant (e1CovarianceRatio 24630 (mW 12315) (1/10^6) rowEps))) /
    (712/10000 - 24630*(1+1/10^6)*((84043/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24630 (mW 12315) /
    ((1/10^5) * ((mW 12315 : ℝ)*24630*((mW 12315 : ℝ)+24630+1)))^2 +
  8*(mW 12315 : ℝ)*24630*(24630+2)*(24630+3) /
    ((1/1000)*((mW 12315 : ℝ)*24630*(24630+2)))^2 +
  covarianceVarianceBound 24630 (mW 12315) /
    ((1/1000)*covarianceMeanBound 24630 (mW 12315))^2 +
  normVarianceBound 24630 (mW 12315) / (3*inputVarianceMean 24630 (mW 12315))^2

end BstLean.Part260.Row12315
#eval (do IO.println s!"P260 END 12315 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12316 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12316
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12316 = 207321279667020 := by
  have hu : mW 12316 ≤ 207321279667020 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12316 ≤ 207321279667019 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12316)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24632 ^ 2)
    ((6250000000000000000/967296378040297338124913))
    ((25000000000000000000/3869028432528509862825413)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24632) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24632 : ℝ)^2 / (mW 12316 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2100903/1000000000000))/2) * ((1-firstRatio 24632) * √(1-firstRatio 24632) *
      sixthConstant (e1CovarianceRatio 24632 (mW 12316) (1/10^6) rowEps))) /
    (712/10000 - 24632*(1+1/10^6)*((2100903/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24632 (mW 12316) /
    ((1/10^5) * ((mW 12316 : ℝ)*24632*((mW 12316 : ℝ)+24632+1)))^2 +
  8*(mW 12316 : ℝ)*24632*(24632+2)*(24632+3) /
    ((1/1000)*((mW 12316 : ℝ)*24632*(24632+2)))^2 +
  covarianceVarianceBound 24632 (mW 12316) /
    ((1/1000)*covarianceMeanBound 24632 (mW 12316))^2 +
  normVarianceBound 24632 (mW 12316) / (3*inputVarianceMean 24632 (mW 12316))^2

end BstLean.Part260.Row12316
#eval (do IO.println s!"P260 END 12316 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12317 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12317
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12317 = 207380202866788 := by
  have hu : mW 12317 ≤ 207380202866788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12317 ≤ 207380202866787 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12317)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24634 ^ 2)
    ((25000000000000000000/3869499671426548331823499))
    ((25000000000000000000/3869342591793868842149259)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24634) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24634 : ℝ)^2 / (mW 12317 : ℝ)) * (1 + 1/10^6)^2 *
    √(((210073/100000000000))/2) * ((1-firstRatio 24634) * √(1-firstRatio 24634) *
      sixthConstant (e1CovarianceRatio 24634 (mW 12317) (1/10^6) rowEps))) /
    (712/10000 - 24634*(1+1/10^6)*((210073/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24634 (mW 12317) /
    ((1/10^5) * ((mW 12317 : ℝ)*24634*((mW 12317 : ℝ)+24634+1)))^2 +
  8*(mW 12317 : ℝ)*24634*(24634+2)*(24634+3) /
    ((1/1000)*((mW 12317 : ℝ)*24634*(24634+2)))^2 +
  covarianceVarianceBound 24634 (mW 12317) /
    ((1/1000)*covarianceMeanBound 24634 (mW 12317))^2 +
  normVarianceBound 24634 (mW 12317) / (3*inputVarianceMean 24634 (mW 12317))^2

end BstLean.Part260.Row12317
#eval (do IO.println s!"P260 END 12317 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12318 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12318
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12318 = 207439138027501 := by
  have hu : mW 12318 ≤ 207439138027501 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12318 ≤ 207439138027500 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12318)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24636 ^ 2)
    ((12500000000000000000/1934906915345953655573673))
    ((5000000000000000000/773931350211845564294621)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24636) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24636 : ℝ)^2 / (mW 12318 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1050279/500000000000))/2) * ((1-firstRatio 24636) * √(1-firstRatio 24636) *
      sixthConstant (e1CovarianceRatio 24636 (mW 12318) (1/10^6) rowEps))) /
    (712/10000 - 24636*(1+1/10^6)*((1050279/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24636 (mW 12318) /
    ((1/10^5) * ((mW 12318 : ℝ)*24636*((mW 12318 : ℝ)+24636+1)))^2 +
  8*(mW 12318 : ℝ)*24636*(24636+2)*(24636+3) /
    ((1/1000)*((mW 12318 : ℝ)*24636*(24636+2)))^2 +
  covarianceVarianceBound 24636 (mW 12318) /
    ((1/1000)*covarianceMeanBound 24636 (mW 12318))^2 +
  normVarianceBound 24636 (mW 12318) / (3*inputVarianceMean 24636 (mW 12318))^2

end BstLean.Part260.Row12318
#eval (do IO.println s!"P260 END 12318 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12319 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12319
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12319 = 207498085150615 := by
  have hu : mW 12319 ≤ 207498085150615 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12319 ≤ 207498085150614 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12319)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24638 ^ 2)
    ((25000000000000000000/3870127989957266290471193))
    ((25000000000000000000/3869970910324586800796951)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24638) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24638 : ℝ)^2 / (mW 12319 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1050193/500000000000))/2) * ((1-firstRatio 24638) * √(1-firstRatio 24638) *
      sixthConstant (e1CovarianceRatio 24638 (mW 12319) (1/10^6) rowEps))) /
    (712/10000 - 24638*(1+1/10^6)*((1050193/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24638 (mW 12319) /
    ((1/10^5) * ((mW 12319 : ℝ)*24638*((mW 12319 : ℝ)+24638+1)))^2 +
  8*(mW 12319 : ℝ)*24638*(24638+2)*(24638+3) /
    ((1/1000)*((mW 12319 : ℝ)*24638*(24638+2)))^2 +
  covarianceVarianceBound 24638 (mW 12319) /
    ((1/1000)*covarianceMeanBound 24638 (mW 12319))^2 +
  normVarianceBound 24638 (mW 12319) / (3*inputVarianceMean 24638 (mW 12319))^2

end BstLean.Part260.Row12319
#eval (do IO.println s!"P260 END 12319 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12320 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12320
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12320 = 207557044237586 := by
  have hu : mW 12320 ≤ 207557044237586 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12320 ≤ 207557044237585 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12320)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24640 ^ 2)
    ((156250000000000000/24190263432641407936219))
    ((25000000000000000000/3870285069589945780120797)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24640) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24640 : ℝ)^2 / (mW 12320 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2100213/1000000000000))/2) * ((1-firstRatio 24640) * √(1-firstRatio 24640) *
      sixthConstant (e1CovarianceRatio 24640 (mW 12320) (1/10^6) rowEps))) /
    (712/10000 - 24640*(1+1/10^6)*((2100213/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24640 (mW 12320) /
    ((1/10^5) * ((mW 12320 : ℝ)*24640*((mW 12320 : ℝ)+24640+1)))^2 +
  8*(mW 12320 : ℝ)*24640*(24640+2)*(24640+3) /
    ((1/1000)*((mW 12320 : ℝ)*24640*(24640+2)))^2 +
  covarianceVarianceBound 24640 (mW 12320) /
    ((1/1000)*covarianceMeanBound 24640 (mW 12320))^2 +
  normVarianceBound 24640 (mW 12320) / (3*inputVarianceMean 24640 (mW 12320))^2

end BstLean.Part260.Row12320
#eval (do IO.println s!"P260 END 12320 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12321 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12321
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12321 = 207616015289871 := by
  have hu : mW 12321 ≤ 207616015289871 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12321 ≤ 207616015289870 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12321)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24642 ^ 2)
    ((25000000000000000000/3870756308487984249118887))
    ((25000000000000000000/3870599228855304759444643)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24642) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24642 : ℝ)^2 / (mW 12321 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2100041/1000000000000))/2) * ((1-firstRatio 24642) * √(1-firstRatio 24642) *
      sixthConstant (e1CovarianceRatio 24642 (mW 12321) (1/10^6) rowEps))) /
    (712/10000 - 24642*(1+1/10^6)*((2100041/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24642 (mW 12321) /
    ((1/10^5) * ((mW 12321 : ℝ)*24642*((mW 12321 : ℝ)+24642+1)))^2 +
  8*(mW 12321 : ℝ)*24642*(24642+2)*(24642+3) /
    ((1/1000)*((mW 12321 : ℝ)*24642*(24642+2)))^2 +
  covarianceVarianceBound 24642 (mW 12321) /
    ((1/1000)*covarianceMeanBound 24642 (mW 12321))^2 +
  normVarianceBound 24642 (mW 12321) / (3*inputVarianceMean 24642 (mW 12321))^2

end BstLean.Part260.Row12321
#eval (do IO.println s!"P260 END 12321 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12322 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12322
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12322 = 207674998308928 := by
  have hu : mW 12322 ≤ 207674998308928 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12322 ≤ 207674998308927 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12322)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24644 ^ 2)
    ((12500000000000000000/1935535233876671614221367))
    ((25000000000000000000/3870913388120663738768489)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24644) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24644 : ℝ)^2 / (mW 12322 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2099869/1000000000000))/2) * ((1-firstRatio 24644) * √(1-firstRatio 24644) *
      sixthConstant (e1CovarianceRatio 24644 (mW 12322) (1/10^6) rowEps))) /
    (712/10000 - 24644*(1+1/10^6)*((2099869/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24644 (mW 12322) /
    ((1/10^5) * ((mW 12322 : ℝ)*24644*((mW 12322 : ℝ)+24644+1)))^2 +
  8*(mW 12322 : ℝ)*24644*(24644+2)*(24644+3) /
    ((1/1000)*((mW 12322 : ℝ)*24644*(24644+2)))^2 +
  covarianceVarianceBound 24644 (mW 12322) /
    ((1/1000)*covarianceMeanBound 24644 (mW 12322))^2 +
  normVarianceBound 24644 (mW 12322) / (3*inputVarianceMean 24644 (mW 12322))^2

end BstLean.Part260.Row12322
#eval (do IO.println s!"P260 END 12322 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12323 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12323
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12323 = 207733993296214 := by
  have hu : mW 12323 ≤ 207733993296214 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12323 ≤ 207733993296213 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12323)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24646 ^ 2)
    ((25000000000000000000/3871384627018702207766581))
    ((5000000000000000000/774245509477204543618467)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24646) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24646 : ℝ)^2 / (mW 12323 : ℝ)) * (1 + 1/10^6)^2 *
    √(((131231/62500000000))/2) * ((1-firstRatio 24646) * √(1-firstRatio 24646) *
      sixthConstant (e1CovarianceRatio 24646 (mW 12323) (1/10^6) rowEps))) /
    (712/10000 - 24646*(1+1/10^6)*((131231/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24646 (mW 12323) /
    ((1/10^5) * ((mW 12323 : ℝ)*24646*((mW 12323 : ℝ)+24646+1)))^2 +
  8*(mW 12323 : ℝ)*24646*(24646+2)*(24646+3) /
    ((1/1000)*((mW 12323 : ℝ)*24646*(24646+2)))^2 +
  covarianceVarianceBound 24646 (mW 12323) /
    ((1/1000)*covarianceMeanBound 24646 (mW 12323))^2 +
  normVarianceBound 24646 (mW 12323) / (3*inputVarianceMean 24646 (mW 12323))^2

end BstLean.Part260.Row12323
#eval (do IO.println s!"P260 END 12323 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12324 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12324
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12324 = 207793000253184 := by
  have hu : mW 12324 ≤ 207793000253184 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12324 ≤ 207793000253183 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12324)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24648 ^ 2)
    ((6250000000000000000/967924696571015296772607))
    ((25000000000000000000/3871541706651381697416181)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24648) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24648 : ℝ)^2 / (mW 12324 : ℝ)) * (1 + 1/10^6)^2 *
    √(((524881/250000000000))/2) * ((1-firstRatio 24648) * √(1-firstRatio 24648) *
      sixthConstant (e1CovarianceRatio 24648 (mW 12324) (1/10^6) rowEps))) /
    (712/10000 - 24648*(1+1/10^6)*((524881/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24648 (mW 12324) /
    ((1/10^5) * ((mW 12324 : ℝ)*24648*((mW 12324 : ℝ)+24648+1)))^2 +
  8*(mW 12324 : ℝ)*24648*(24648+2)*(24648+3) /
    ((1/1000)*((mW 12324 : ℝ)*24648*(24648+2)))^2 +
  covarianceVarianceBound 24648 (mW 12324) /
    ((1/1000)*covarianceMeanBound 24648 (mW 12324))^2 +
  normVarianceBound 24648 (mW 12324) / (3*inputVarianceMean 24648 (mW 12324))^2

end BstLean.Part260.Row12324
#eval (do IO.println s!"P260 END 12324 0 {← IO.monoMsNow}" : IO Unit)
