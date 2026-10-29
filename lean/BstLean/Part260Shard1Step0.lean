import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part259Data5
import BstLean.Part259Data6
import BstLean.Part259Data7
import BstLean.Part259Data8
import BstLean.Part259Data9
#eval (do IO.println s!"P260 START 12250 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12250
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12250 = 203458721178754 := by
  have hu : mW 12250 ≤ 203458721178754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12250 ≤ 203458721178753 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12250)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24500 ^ 2)
    ((100000000000000000/15393804002589986868503))
    ((25000000000000000000/3848293921014817227451577)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24500) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24500 : ℝ)^2 / (mW 12250 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2112347/1000000000000))/2) * ((1-firstRatio 24500) * √(1-firstRatio 24500) *
      sixthConstant (e1CovarianceRatio 24500 (mW 12250) (1/10^6) rowEps))) /
    (712/10000 - 24500*(1+1/10^6)*((2112347/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24500 (mW 12250) /
    ((1/10^5) * ((mW 12250 : ℝ)*24500*((mW 12250 : ℝ)+24500+1)))^2 +
  8*(mW 12250 : ℝ)*24500*(24500+2)*(24500+3) /
    ((1/1000)*((mW 12250 : ℝ)*24500*(24500+2)))^2 +
  covarianceVarianceBound 24500 (mW 12250) /
    ((1/1000)*covarianceMeanBound 24500 (mW 12250))^2 +
  normVarianceBound 24500 (mW 12250) / (3*inputVarianceMean 24500 (mW 12250))^2

end BstLean.Part260.Row12250
#eval (do IO.println s!"P260 END 12250 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12251 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12251
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12251 = 203516858173931 := by
  have hu : mW 12251 ≤ 203516858173931 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12251 ≤ 203516858173930 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12251)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24502 ^ 2)
    ((25000000000000000000/3848765159912855696449597))
    ((25000000000000000000/3848608080280176206775423)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24502) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24502 : ℝ)^2 / (mW 12251 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2112173/1000000000000))/2) * ((1-firstRatio 24502) * √(1-firstRatio 24502) *
      sixthConstant (e1CovarianceRatio 24502 (mW 12251) (1/10^6) rowEps))) /
    (712/10000 - 24502*(1+1/10^6)*((2112173/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24502 (mW 12251) /
    ((1/10^5) * ((mW 12251 : ℝ)*24502*((mW 12251 : ℝ)+24502+1)))^2 +
  8*(mW 12251 : ℝ)*24502*(24502+2)*(24502+3) /
    ((1/1000)*((mW 12251 : ℝ)*24502*(24502+2)))^2 +
  covarianceVarianceBound 24502 (mW 12251) /
    ((1/1000)*covarianceMeanBound 24502 (mW 12251))^2 +
  normVarianceBound 24502 (mW 12251) / (3*inputVarianceMean 24502 (mW 12251))^2

end BstLean.Part260.Row12251
#eval (do IO.println s!"P260 END 12251 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12252 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12252
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12252 = 203575007034044 := by
  have hu : mW 12252 ≤ 203575007034044 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12252 ≤ 203575007034043 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12252)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24504 ^ 2)
    ((6250000000000000000/962269829794553668943361))
    ((25000000000000000000/3848922239545535186099269)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24504) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24504 : ℝ)^2 / (mW 12252 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1055999/500000000000))/2) * ((1-firstRatio 24504) * √(1-firstRatio 24504) *
      sixthConstant (e1CovarianceRatio 24504 (mW 12252) (1/10^6) rowEps))) /
    (712/10000 - 24504*(1+1/10^6)*((1055999/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24504 (mW 12252) /
    ((1/10^5) * ((mW 12252 : ℝ)*24504*((mW 12252 : ℝ)+24504+1)))^2 +
  8*(mW 12252 : ℝ)*24504*(24504+2)*(24504+3) /
    ((1/1000)*((mW 12252 : ℝ)*24504*(24504+2)))^2 +
  covarianceVarianceBound 24504 (mW 12252) /
    ((1/1000)*covarianceMeanBound 24504 (mW 12252))^2 +
  normVarianceBound 24504 (mW 12252) / (3*inputVarianceMean 24504 (mW 12252))^2

end BstLean.Part260.Row12252
#eval (do IO.println s!"P260 END 12252 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12253 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12253
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12253 = 203633167760544 := by
  have hu : mW 12253 ≤ 203633167760544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12253 ≤ 203633167760543 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12253)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24506 ^ 2)
    ((25000000000000000000/3849393478443573655097291))
    ((5000000000000000000/769847279762178833084623)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24506) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24506 : ℝ)^2 / (mW 12253 : ℝ)) * (1 + 1/10^6)^2 *
    √(((131989/62500000000))/2) * ((1-firstRatio 24506) * √(1-firstRatio 24506) *
      sixthConstant (e1CovarianceRatio 24506 (mW 12253) (1/10^6) rowEps))) /
    (712/10000 - 24506*(1+1/10^6)*((131989/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24506 (mW 12253) /
    ((1/10^5) * ((mW 12253 : ℝ)*24506*((mW 12253 : ℝ)+24506+1)))^2 +
  8*(mW 12253 : ℝ)*24506*(24506+2)*(24506+3) /
    ((1/1000)*((mW 12253 : ℝ)*24506*(24506+2)))^2 +
  covarianceVarianceBound 24506 (mW 12253) /
    ((1/1000)*covarianceMeanBound 24506 (mW 12253))^2 +
  normVarianceBound 24506 (mW 12253) / (3*inputVarianceMean 24506 (mW 12253))^2

end BstLean.Part260.Row12253
#eval (do IO.println s!"P260 END 12253 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12254 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12254
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12254 = 203691340354884 := by
  have hu : mW 12254 ≤ 203691340354884 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12254 ≤ 203691340354883 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12254)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24508 ^ 2)
    ((12500000000000000000/1924853818854466317210569))
    ((25000000000000000000/3849550558076253144746961)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24508) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24508 : ℝ)^2 / (mW 12254 : ℝ)) * (1 + 1/10^6)^2 *
    √(((42233/20000000000))/2) * ((1-firstRatio 24508) * √(1-firstRatio 24508) *
      sixthConstant (e1CovarianceRatio 24508 (mW 12254) (1/10^6) rowEps))) /
    (712/10000 - 24508*(1+1/10^6)*((42233/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24508 (mW 12254) /
    ((1/10^5) * ((mW 12254 : ℝ)*24508*((mW 12254 : ℝ)+24508+1)))^2 +
  8*(mW 12254 : ℝ)*24508*(24508+2)*(24508+3) /
    ((1/1000)*((mW 12254 : ℝ)*24508*(24508+2)))^2 +
  covarianceVarianceBound 24508 (mW 12254) /
    ((1/1000)*covarianceMeanBound 24508 (mW 12254))^2 +
  normVarianceBound 24508 (mW 12254) / (3*inputVarianceMean 24508 (mW 12254))^2

end BstLean.Part260.Row12254
#eval (do IO.println s!"P260 END 12254 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12255 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12255
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12255 = 203749524818518 := by
  have hu : mW 12255 ≤ 203749524818518 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12255 ≤ 203749524818517 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12255)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24510 ^ 2)
    ((5000000000000000000/770004359394858322748997))
    ((25000000000000000000/3849864717341612124070807)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24510) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24510 : ℝ)^2 / (mW 12255 : ℝ)) * (1 + 1/10^6)^2 *
    √(((84459/40000000000))/2) * ((1-firstRatio 24510) * √(1-firstRatio 24510) *
      sixthConstant (e1CovarianceRatio 24510 (mW 12255) (1/10^6) rowEps))) /
    (712/10000 - 24510*(1+1/10^6)*((84459/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24510 (mW 12255) /
    ((1/10^5) * ((mW 12255 : ℝ)*24510*((mW 12255 : ℝ)+24510+1)))^2 +
  8*(mW 12255 : ℝ)*24510*(24510+2)*(24510+3) /
    ((1/1000)*((mW 12255 : ℝ)*24510*(24510+2)))^2 +
  covarianceVarianceBound 24510 (mW 12255) /
    ((1/1000)*covarianceMeanBound 24510 (mW 12255))^2 +
  normVarianceBound 24510 (mW 12255) / (3*inputVarianceMean 24510 (mW 12255))^2

end BstLean.Part260.Row12255
#eval (do IO.println s!"P260 END 12255 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12256 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12256
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12256 = 203807721152898 := by
  have hu : mW 12256 ≤ 203807721152898 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12256 ≤ 203807721152897 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12256)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24512 ^ 2)
    ((781250000000000000/120322998632489081033401))
    ((25000000000000000000/3850178876606971103394653)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24512) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24512 : ℝ)^2 / (mW 12256 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2111301/1000000000000))/2) * ((1-firstRatio 24512) * √(1-firstRatio 24512) *
      sixthConstant (e1CovarianceRatio 24512 (mW 12256) (1/10^6) rowEps))) /
    (712/10000 - 24512*(1+1/10^6)*((2111301/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24512 (mW 12256) /
    ((1/10^5) * ((mW 12256 : ℝ)*24512*((mW 12256 : ℝ)+24512+1)))^2 +
  8*(mW 12256 : ℝ)*24512*(24512+2)*(24512+3) /
    ((1/1000)*((mW 12256 : ℝ)*24512*(24512+2)))^2 +
  covarianceVarianceBound 24512 (mW 12256) /
    ((1/1000)*covarianceMeanBound 24512 (mW 12256))^2 +
  normVarianceBound 24512 (mW 12256) / (3*inputVarianceMean 24512 (mW 12256))^2

end BstLean.Part260.Row12256
#eval (do IO.println s!"P260 END 12256 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12257 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12257
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12257 = 203865929359478 := by
  have hu : mW 12257 ≤ 203865929359478 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12257 ≤ 203865929359477 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12257)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24514 ^ 2)
    ((25000000000000000000/3850650115505009572392679))
    ((25000000000000000000/3850493035872330082718499)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24514) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24514 : ℝ)^2 / (mW 12257 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2111127/1000000000000))/2) * ((1-firstRatio 24514) * √(1-firstRatio 24514) *
      sixthConstant (e1CovarianceRatio 24514 (mW 12257) (1/10^6) rowEps))) /
    (712/10000 - 24514*(1+1/10^6)*((2111127/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24514 (mW 12257) /
    ((1/10^5) * ((mW 12257 : ℝ)*24514*((mW 12257 : ℝ)+24514+1)))^2 +
  8*(mW 12257 : ℝ)*24514*(24514+2)*(24514+3) /
    ((1/1000)*((mW 12257 : ℝ)*24514*(24514+2)))^2 +
  covarianceVarianceBound 24514 (mW 12257) /
    ((1/1000)*covarianceMeanBound 24514 (mW 12257))^2 +
  normVarianceBound 24514 (mW 12257) / (3*inputVarianceMean 24514 (mW 12257))^2

end BstLean.Part260.Row12257
#eval (do IO.println s!"P260 END 12257 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12258 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12258
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12258 = 203924149439710 := by
  have hu : mW 12258 ≤ 203924149439710 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12258 ≤ 203924149439709 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12258)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24516 ^ 2)
    ((12500000000000000000/1925482137385184275858263))
    ((5000000000000000000/770161439027537812408469)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24516) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24516 : ℝ)^2 / (mW 12258 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2110953/1000000000000))/2) * ((1-firstRatio 24516) * √(1-firstRatio 24516) *
      sixthConstant (e1CovarianceRatio 24516 (mW 12258) (1/10^6) rowEps))) /
    (712/10000 - 24516*(1+1/10^6)*((2110953/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24516 (mW 12258) /
    ((1/10^5) * ((mW 12258 : ℝ)*24516*((mW 12258 : ℝ)+24516+1)))^2 +
  8*(mW 12258 : ℝ)*24516*(24516+2)*(24516+3) /
    ((1/1000)*((mW 12258 : ℝ)*24516*(24516+2)))^2 +
  covarianceVarianceBound 24516 (mW 12258) /
    ((1/1000)*covarianceMeanBound 24516 (mW 12258))^2 +
  normVarianceBound 24516 (mW 12258) / (3*inputVarianceMean 24516 (mW 12258))^2

end BstLean.Part260.Row12258
#eval (do IO.println s!"P260 END 12258 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12259 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12259
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12259 = 203982381395048 := by
  have hu : mW 12259 ≤ 203982381395048 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12259 ≤ 203982381395047 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12259)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24518 ^ 2)
    ((25000000000000000000/3851278434035727531040373))
    ((25000000000000000000/3851121354403048041366191)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24518) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24518 : ℝ)^2 / (mW 12259 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2110779/1000000000000))/2) * ((1-firstRatio 24518) * √(1-firstRatio 24518) *
      sixthConstant (e1CovarianceRatio 24518 (mW 12259) (1/10^6) rowEps))) /
    (712/10000 - 24518*(1+1/10^6)*((2110779/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24518 (mW 12259) /
    ((1/10^5) * ((mW 12259 : ℝ)*24518*((mW 12259 : ℝ)+24518+1)))^2 +
  8*(mW 12259 : ℝ)*24518*(24518+2)*(24518+3) /
    ((1/1000)*((mW 12259 : ℝ)*24518*(24518+2)))^2 +
  covarianceVarianceBound 24518 (mW 12259) /
    ((1/1000)*covarianceMeanBound 24518 (mW 12259))^2 +
  normVarianceBound 24518 (mW 12259) / (3*inputVarianceMean 24518 (mW 12259))^2

end BstLean.Part260.Row12259
#eval (do IO.println s!"P260 END 12259 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12260 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12260
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12260 = 204040625226944 := by
  have hu : mW 12260 ≤ 204040625226944 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12260 ≤ 204040625226943 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12260)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24520 ^ 2)
    ((1250000000000000000/192579629665054325518211))
    ((25000000000000000000/3851435513668407020690037)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24520) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24520 : ℝ)^2 / (mW 12260 : ℝ)) * (1 + 1/10^6)^2 *
    √(((422121/200000000000))/2) * ((1-firstRatio 24520) * √(1-firstRatio 24520) *
      sixthConstant (e1CovarianceRatio 24520 (mW 12260) (1/10^6) rowEps))) /
    (712/10000 - 24520*(1+1/10^6)*((422121/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24520 (mW 12260) /
    ((1/10^5) * ((mW 12260 : ℝ)*24520*((mW 12260 : ℝ)+24520+1)))^2 +
  8*(mW 12260 : ℝ)*24520*(24520+2)*(24520+3) /
    ((1/1000)*((mW 12260 : ℝ)*24520*(24520+2)))^2 +
  covarianceVarianceBound 24520 (mW 12260) /
    ((1/1000)*covarianceMeanBound 24520 (mW 12260))^2 +
  normVarianceBound 24520 (mW 12260) / (3*inputVarianceMean 24520 (mW 12260))^2

end BstLean.Part260.Row12260
#eval (do IO.println s!"P260 END 12260 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12261 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12261
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12261 = 204098880936853 := by
  have hu : mW 12261 ≤ 204098880936853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12261 ≤ 204098880936852 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12261)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24522 ^ 2)
    ((25000000000000000000/3851906752566445489688067))
    ((25000000000000000000/3851749672933766000013883)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24522) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24522 : ℝ)^2 / (mW 12261 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2110431/1000000000000))/2) * ((1-firstRatio 24522) * √(1-firstRatio 24522) *
      sixthConstant (e1CovarianceRatio 24522 (mW 12261) (1/10^6) rowEps))) /
    (712/10000 - 24522*(1+1/10^6)*((2110431/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24522 (mW 12261) /
    ((1/10^5) * ((mW 12261 : ℝ)*24522*((mW 12261 : ℝ)+24522+1)))^2 +
  8*(mW 12261 : ℝ)*24522*(24522+2)*(24522+3) /
    ((1/1000)*((mW 12261 : ℝ)*24522*(24522+2)))^2 +
  covarianceVarianceBound 24522 (mW 12261) /
    ((1/1000)*covarianceMeanBound 24522 (mW 12261))^2 +
  normVarianceBound 24522 (mW 12261) / (3*inputVarianceMean 24522 (mW 12261))^2

end BstLean.Part260.Row12261
#eval (do IO.println s!"P260 END 12261 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12262 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12262
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12262 = 204157148526226 := by
  have hu : mW 12262 ≤ 204157148526226 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12262 ≤ 204157148526225 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12262)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24524 ^ 2)
    ((12500000000000000000/1926110455915902234505957))
    ((25000000000000000000/3852063832199124979337729)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24524) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24524 : ℝ)^2 / (mW 12262 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2110257/1000000000000))/2) * ((1-firstRatio 24524) * √(1-firstRatio 24524) *
      sixthConstant (e1CovarianceRatio 24524 (mW 12262) (1/10^6) rowEps))) /
    (712/10000 - 24524*(1+1/10^6)*((2110257/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24524 (mW 12262) /
    ((1/10^5) * ((mW 12262 : ℝ)*24524*((mW 12262 : ℝ)+24524+1)))^2 +
  8*(mW 12262 : ℝ)*24524*(24524+2)*(24524+3) /
    ((1/1000)*((mW 12262 : ℝ)*24524*(24524+2)))^2 +
  covarianceVarianceBound 24524 (mW 12262) /
    ((1/1000)*covarianceMeanBound 24524 (mW 12262))^2 +
  normVarianceBound 24524 (mW 12262) / (3*inputVarianceMean 24524 (mW 12262))^2

end BstLean.Part260.Row12262
#eval (do IO.println s!"P260 END 12262 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12263 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12263
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12263 = 204215427996519 := by
  have hu : mW 12263 ≤ 204215427996519 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12263 ≤ 204215427996518 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12263)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24526 ^ 2)
    ((25000000000000000000/3852535071097163448335761))
    ((1000000000000000000/154095119658579358346463)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24526) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24526 : ℝ)^2 / (mW 12263 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2110083/1000000000000))/2) * ((1-firstRatio 24526) * √(1-firstRatio 24526) *
      sixthConstant (e1CovarianceRatio 24526 (mW 12263) (1/10^6) rowEps))) /
    (712/10000 - 24526*(1+1/10^6)*((2110083/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24526 (mW 12263) /
    ((1/10^5) * ((mW 12263 : ℝ)*24526*((mW 12263 : ℝ)+24526+1)))^2 +
  8*(mW 12263 : ℝ)*24526*(24526+2)*(24526+3) /
    ((1/1000)*((mW 12263 : ℝ)*24526*(24526+2)))^2 +
  covarianceVarianceBound 24526 (mW 12263) /
    ((1/1000)*covarianceMeanBound 24526 (mW 12263))^2 +
  normVarianceBound 24526 (mW 12263) / (3*inputVarianceMean 24526 (mW 12263))^2

end BstLean.Part260.Row12263
#eval (do IO.println s!"P260 END 12263 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12264 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12264
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12264 = 204273719349183 := by
  have hu : mW 12264 ≤ 204273719349183 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12264 ≤ 204273719349182 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12264)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24528 ^ 2)
    ((3125000000000000000/481606153795315303457451))
    ((25000000000000000000/3852692150729842937985421)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24528) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24528 : ℝ)^2 / (mW 12264 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2109909/1000000000000))/2) * ((1-firstRatio 24528) * √(1-firstRatio 24528) *
      sixthConstant (e1CovarianceRatio 24528 (mW 12264) (1/10^6) rowEps))) /
    (712/10000 - 24528*(1+1/10^6)*((2109909/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24528 (mW 12264) /
    ((1/10^5) * ((mW 12264 : ℝ)*24528*((mW 12264 : ℝ)+24528+1)))^2 +
  8*(mW 12264 : ℝ)*24528*(24528+2)*(24528+3) /
    ((1/1000)*((mW 12264 : ℝ)*24528*(24528+2)))^2 +
  covarianceVarianceBound 24528 (mW 12264) /
    ((1/1000)*covarianceMeanBound 24528 (mW 12264))^2 +
  normVarianceBound 24528 (mW 12264) / (3*inputVarianceMean 24528 (mW 12264))^2

end BstLean.Part260.Row12264
#eval (do IO.println s!"P260 END 12264 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12265 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12265
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12265 = 204332022585673 := by
  have hu : mW 12265 ≤ 204332022585673 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12265 ≤ 204332022585672 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12265)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24530 ^ 2)
    ((5000000000000000000/770632677925576281396691))
    ((25000000000000000000/3853006309995201917309267)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24530) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24530 : ℝ)^2 / (mW 12265 : ℝ)) * (1 + 1/10^6)^2 *
    √(((421947/200000000000))/2) * ((1-firstRatio 24530) * √(1-firstRatio 24530) *
      sixthConstant (e1CovarianceRatio 24530 (mW 12265) (1/10^6) rowEps))) /
    (712/10000 - 24530*(1+1/10^6)*((421947/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24530 (mW 12265) /
    ((1/10^5) * ((mW 12265 : ℝ)*24530*((mW 12265 : ℝ)+24530+1)))^2 +
  8*(mW 12265 : ℝ)*24530*(24530+2)*(24530+3) /
    ((1/1000)*((mW 12265 : ℝ)*24530*(24530+2)))^2 +
  covarianceVarianceBound 24530 (mW 12265) /
    ((1/1000)*covarianceMeanBound 24530 (mW 12265))^2 +
  normVarianceBound 24530 (mW 12265) / (3*inputVarianceMean 24530 (mW 12265))^2

end BstLean.Part260.Row12265
#eval (do IO.println s!"P260 END 12265 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12266 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12266
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12266 = 204390337707442 := by
  have hu : mW 12266 ≤ 204390337707442 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12266 ≤ 204390337707441 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12266)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24532 ^ 2)
    ((12500000000000000000/1926738774446620193153651))
    ((25000000000000000000/3853320469260560896633113)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24532) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24532 : ℝ)^2 / (mW 12266 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2109561/1000000000000))/2) * ((1-firstRatio 24532) * √(1-firstRatio 24532) *
      sixthConstant (e1CovarianceRatio 24532 (mW 12266) (1/10^6) rowEps))) /
    (712/10000 - 24532*(1+1/10^6)*((2109561/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24532 (mW 12266) /
    ((1/10^5) * ((mW 12266 : ℝ)*24532*((mW 12266 : ℝ)+24532+1)))^2 +
  8*(mW 12266 : ℝ)*24532*(24532+2)*(24532+3) /
    ((1/1000)*((mW 12266 : ℝ)*24532*(24532+2)))^2 +
  covarianceVarianceBound 24532 (mW 12266) /
    ((1/1000)*covarianceMeanBound 24532 (mW 12266))^2 +
  normVarianceBound 24532 (mW 12266) / (3*inputVarianceMean 24532 (mW 12266))^2

end BstLean.Part260.Row12266
#eval (do IO.println s!"P260 END 12266 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12267 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12267
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12267 = 204448664715943 := by
  have hu : mW 12267 ≤ 204448664715943 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12267 ≤ 204448664715942 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12267)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24534 ^ 2)
    ((25000000000000000000/3853791708158599365631149))
    ((25000000000000000000/3853634628525919875956959)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24534) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24534 : ℝ)^2 / (mW 12267 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2109387/1000000000000))/2) * ((1-firstRatio 24534) * √(1-firstRatio 24534) *
      sixthConstant (e1CovarianceRatio 24534 (mW 12267) (1/10^6) rowEps))) /
    (712/10000 - 24534*(1+1/10^6)*((2109387/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24534 (mW 12267) /
    ((1/10^5) * ((mW 12267 : ℝ)*24534*((mW 12267 : ℝ)+24534+1)))^2 +
  8*(mW 12267 : ℝ)*24534*(24534+2)*(24534+3) /
    ((1/1000)*((mW 12267 : ℝ)*24534*(24534+2)))^2 +
  covarianceVarianceBound 24534 (mW 12267) /
    ((1/1000)*covarianceMeanBound 24534 (mW 12267))^2 +
  normVarianceBound 24534 (mW 12267) / (3*inputVarianceMean 24534 (mW 12267))^2

end BstLean.Part260.Row12267
#eval (do IO.println s!"P260 END 12267 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12268 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12268
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12268 = 204507003612631 := by
  have hu : mW 12268 ≤ 204507003612631 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12268 ≤ 204507003612630 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12268)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24536 ^ 2)
    ((6250000000000000000/963526466855989586238749))
    ((5000000000000000000/770789757558255771056161)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24536) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24536 : ℝ)^2 / (mW 12268 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2109213/1000000000000))/2) * ((1-firstRatio 24536) * √(1-firstRatio 24536) *
      sixthConstant (e1CovarianceRatio 24536 (mW 12268) (1/10^6) rowEps))) /
    (712/10000 - 24536*(1+1/10^6)*((2109213/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24536 (mW 12268) /
    ((1/10^5) * ((mW 12268 : ℝ)*24536*((mW 12268 : ℝ)+24536+1)))^2 +
  8*(mW 12268 : ℝ)*24536*(24536+2)*(24536+3) /
    ((1/1000)*((mW 12268 : ℝ)*24536*(24536+2)))^2 +
  covarianceVarianceBound 24536 (mW 12268) /
    ((1/1000)*covarianceMeanBound 24536 (mW 12268))^2 +
  normVarianceBound 24536 (mW 12268) / (3*inputVarianceMean 24536 (mW 12268))^2

end BstLean.Part260.Row12268
#eval (do IO.println s!"P260 END 12268 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12269 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12269
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12269 = 204565354398959 := by
  have hu : mW 12269 ≤ 204565354398959 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12269 ≤ 204565354398958 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12269)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24538 ^ 2)
    ((25000000000000000000/3854420026689317324278843))
    ((25000000000000000000/3854262947056637834604651)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24538) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24538 : ℝ)^2 / (mW 12269 : ℝ)) * (1 + 1/10^6)^2 *
    √(((26363/12500000000))/2) * ((1-firstRatio 24538) * √(1-firstRatio 24538) *
      sixthConstant (e1CovarianceRatio 24538 (mW 12269) (1/10^6) rowEps))) /
    (712/10000 - 24538*(1+1/10^6)*((26363/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24538 (mW 12269) /
    ((1/10^5) * ((mW 12269 : ℝ)*24538*((mW 12269 : ℝ)+24538+1)))^2 +
  8*(mW 12269 : ℝ)*24538*(24538+2)*(24538+3) /
    ((1/1000)*((mW 12269 : ℝ)*24538*(24538+2)))^2 +
  covarianceVarianceBound 24538 (mW 12269) /
    ((1/1000)*covarianceMeanBound 24538 (mW 12269))^2 +
  normVarianceBound 24538 (mW 12269) / (3*inputVarianceMean 24538 (mW 12269))^2

end BstLean.Part260.Row12269
#eval (do IO.println s!"P260 END 12269 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12270 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12270
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12270 = 204623717076380 := by
  have hu : mW 12270 ≤ 204623717076380 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12270 ≤ 204623717076379 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12270)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24540 ^ 2)
    ((2500000000000000000/385473418595467630360269))
    ((25000000000000000000/3854577106321996813928497)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24540) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24540 : ℝ)^2 / (mW 12270 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1054433/500000000000))/2) * ((1-firstRatio 24540) * √(1-firstRatio 24540) *
      sixthConstant (e1CovarianceRatio 24540 (mW 12270) (1/10^6) rowEps))) /
    (712/10000 - 24540*(1+1/10^6)*((1054433/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24540 (mW 12270) /
    ((1/10^5) * ((mW 12270 : ℝ)*24540*((mW 12270 : ℝ)+24540+1)))^2 +
  8*(mW 12270 : ℝ)*24540*(24540+2)*(24540+3) /
    ((1/1000)*((mW 12270 : ℝ)*24540*(24540+2)))^2 +
  covarianceVarianceBound 24540 (mW 12270) /
    ((1/1000)*covarianceMeanBound 24540 (mW 12270))^2 +
  normVarianceBound 24540 (mW 12270) / (3*inputVarianceMean 24540 (mW 12270))^2

end BstLean.Part260.Row12270
#eval (do IO.println s!"P260 END 12270 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12271 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12271
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12271 = 204682091646349 := by
  have hu : mW 12271 ≤ 204682091646349 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12271 ≤ 204682091646348 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12271)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24542 ^ 2)
    ((25000000000000000000/3855048345220035282926537))
    ((25000000000000000000/3854891265587355793252343)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24542) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24542 : ℝ)^2 / (mW 12271 : ℝ)) * (1 + 1/10^6)^2 *
    √(((527173/250000000000))/2) * ((1-firstRatio 24542) * √(1-firstRatio 24542) *
      sixthConstant (e1CovarianceRatio 24542 (mW 12271) (1/10^6) rowEps))) /
    (712/10000 - 24542*(1+1/10^6)*((527173/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24542 (mW 12271) /
    ((1/10^5) * ((mW 12271 : ℝ)*24542*((mW 12271 : ℝ)+24542+1)))^2 +
  8*(mW 12271 : ℝ)*24542*(24542+2)*(24542+3) /
    ((1/1000)*((mW 12271 : ℝ)*24542*(24542+2)))^2 +
  covarianceVarianceBound 24542 (mW 12271) /
    ((1/1000)*covarianceMeanBound 24542 (mW 12271))^2 +
  normVarianceBound 24542 (mW 12271) / (3*inputVarianceMean 24542 (mW 12271))^2

end BstLean.Part260.Row12271
#eval (do IO.println s!"P260 END 12271 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12272 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12272
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12272 = 204740478110319 := by
  have hu : mW 12272 ≤ 204740478110319 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12272 ≤ 204740478110318 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12272)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24544 ^ 2)
    ((1562500000000000000/240960156530337141390649))
    ((25000000000000000000/3855205424852714772576189)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24544) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24544 : ℝ)^2 / (mW 12272 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1054259/500000000000))/2) * ((1-firstRatio 24544) * √(1-firstRatio 24544) *
      sixthConstant (e1CovarianceRatio 24544 (mW 12272) (1/10^6) rowEps))) /
    (712/10000 - 24544*(1+1/10^6)*((1054259/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24544 (mW 12272) /
    ((1/10^5) * ((mW 12272 : ℝ)*24544*((mW 12272 : ℝ)+24544+1)))^2 +
  8*(mW 12272 : ℝ)*24544*(24544+2)*(24544+3) /
    ((1/1000)*((mW 12272 : ℝ)*24544*(24544+2)))^2 +
  covarianceVarianceBound 24544 (mW 12272) /
    ((1/1000)*covarianceMeanBound 24544 (mW 12272))^2 +
  normVarianceBound 24544 (mW 12272) / (3*inputVarianceMean 24544 (mW 12272))^2

end BstLean.Part260.Row12272
#eval (do IO.println s!"P260 END 12272 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12273 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12273
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12273 = 204798876469745 := by
  have hu : mW 12273 ≤ 204798876469745 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12273 ≤ 204798876469744 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12273)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24546 ^ 2)
    ((25000000000000000000/3855676663750753241574231))
    ((5000000000000000000/771103916823614750380007)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24546) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24546 : ℝ)^2 / (mW 12273 : ℝ)) * (1 + 1/10^6)^2 *
    √(((421669/200000000000))/2) * ((1-firstRatio 24546) * √(1-firstRatio 24546) *
      sixthConstant (e1CovarianceRatio 24546 (mW 12273) (1/10^6) rowEps))) /
    (712/10000 - 24546*(1+1/10^6)*((421669/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24546 (mW 12273) /
    ((1/10^5) * ((mW 12273 : ℝ)*24546*((mW 12273 : ℝ)+24546+1)))^2 +
  8*(mW 12273 : ℝ)*24546*(24546+2)*(24546+3) /
    ((1/1000)*((mW 12273 : ℝ)*24546*(24546+2)))^2 +
  covarianceVarianceBound 24546 (mW 12273) /
    ((1/1000)*covarianceMeanBound 24546 (mW 12273))^2 +
  normVarianceBound 24546 (mW 12273) / (3*inputVarianceMean 24546 (mW 12273))^2

end BstLean.Part260.Row12273
#eval (do IO.println s!"P260 END 12273 0 {← IO.monoMsNow}" : IO Unit)
#eval (do IO.println s!"P260 START 12274 0 {← IO.monoMsNow}" : IO Unit)
namespace BstLean.Part260.Row12274
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12274 = 204857286726081 := by
  have hu : mW 12274 ≤ 204857286726081 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12274 ≤ 204857286726080 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12274)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24548 ^ 2)
    ((12500000000000000000/1927995411508056110449039))
    ((25000000000000000000/3855833743383432731223881)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24548) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24548 : ℝ)^2 / (mW 12274 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2108171/1000000000000))/2) * ((1-firstRatio 24548) * √(1-firstRatio 24548) *
      sixthConstant (e1CovarianceRatio 24548 (mW 12274) (1/10^6) rowEps))) /
    (712/10000 - 24548*(1+1/10^6)*((2108171/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24548 (mW 12274) /
    ((1/10^5) * ((mW 12274 : ℝ)*24548*((mW 12274 : ℝ)+24548+1)))^2 +
  8*(mW 12274 : ℝ)*24548*(24548+2)*(24548+3) /
    ((1/1000)*((mW 12274 : ℝ)*24548*(24548+2)))^2 +
  covarianceVarianceBound 24548 (mW 12274) /
    ((1/1000)*covarianceMeanBound 24548 (mW 12274))^2 +
  normVarianceBound 24548 (mW 12274) / (3*inputVarianceMean 24548 (mW 12274))^2

end BstLean.Part260.Row12274
#eval (do IO.println s!"P260 END 12274 0 {← IO.monoMsNow}" : IO Unit)
