import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar2
namespace BstLean.Part268.WorldRow12400
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12400 = 212312663210329 := by
  have hu : mW 12400 ≤ 212312663210329 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12400 ≤ 212312663210328 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12400)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24800 ^ 2)
    ((62500000000000000/9738937226128359039257))
    ((25000000000000000000/3895417810818664126028477)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24800) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24800 : ℝ)^2 / (mW 12400 : ℝ)) * (1 + 1/10^6)^2 *
    √(((521629/250000000000))/2) * ((1-firstRatio 24800) * √(1-firstRatio 24800) *
      sixthConstant (e1CovarianceRatio 24800 (mW 12400) (1/10^6) rowEps))) /
    (712/10000 - 24800*(1+1/10^6)*((521629/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24800 (mW 12400) /
    ((1/10^5) * ((mW 12400 : ℝ)*24800*((mW 12400 : ℝ)+24800+1)))^2 +
  8*(mW 12400 : ℝ)*24800*(24800+2)*(24800+3) /
    ((1/1000)*((mW 12400 : ℝ)*24800*(24800+2)))^2 +
  covarianceVarianceBound 24800 (mW 12400) /
    ((1/1000)*covarianceMeanBound 24800 (mW 12400))^2 +
  normVarianceBound 24800 (mW 12400) / (3*inputVarianceMean 24800 (mW 12400))^2

end BstLean.Part268.WorldRow12400
namespace BstLean.Part268.WorldRow12401
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12401 = 212372596212987 := by
  have hu : mW 12401 ≤ 212372596212987 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12401 ≤ 212372596212986 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12401)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24802 ^ 2)
    ((25000000000000000000/3895889049716702595026647))
    ((25000000000000000000/3895731970084023105352323)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24802) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24802 : ℝ)^2 / (mW 12401 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1043173/500000000000))/2) * ((1-firstRatio 24802) * √(1-firstRatio 24802) *
      sixthConstant (e1CovarianceRatio 24802 (mW 12401) (1/10^6) rowEps))) /
    (712/10000 - 24802*(1+1/10^6)*((1043173/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24802 (mW 12401) /
    ((1/10^5) * ((mW 12401 : ℝ)*24802*((mW 12401 : ℝ)+24802+1)))^2 +
  8*(mW 12401 : ℝ)*24802*(24802+2)*(24802+3) /
    ((1/1000)*((mW 12401 : ℝ)*24802*(24802+2)))^2 +
  covarianceVarianceBound 24802 (mW 12401) /
    ((1/1000)*covarianceMeanBound 24802 (mW 12401))^2 +
  normVarianceBound 24802 (mW 12401) / (3*inputVarianceMean 24802 (mW 12401))^2

end BstLean.Part268.WorldRow12401
namespace BstLean.Part268.WorldRow12402
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12402 = 212432541299155 := by
  have hu : mW 12402 ≤ 212432541299155 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12402 ≤ 212432541299154 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12402)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24804 ^ 2)
    ((12500000000000000000/1948101604491030787175247))
    ((25000000000000000000/3896046129349382084676169)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24804) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24804 : ℝ)^2 / (mW 12402 : ℝ)) * (1 + 1/10^6)^2 *
    √(((65193/31250000000))/2) * ((1-firstRatio 24804) * √(1-firstRatio 24804) *
      sixthConstant (e1CovarianceRatio 24804 (mW 12402) (1/10^6) rowEps))) /
    (712/10000 - 24804*(1+1/10^6)*((65193/31250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24804 (mW 12402) /
    ((1/10^5) * ((mW 12402 : ℝ)*24804*((mW 12402 : ℝ)+24804+1)))^2 +
  8*(mW 12402 : ℝ)*24804*(24804+2)*(24804+3) /
    ((1/1000)*((mW 12402 : ℝ)*24804*(24804+2)))^2 +
  covarianceVarianceBound 24804 (mW 12402) /
    ((1/1000)*covarianceMeanBound 24804 (mW 12402))^2 +
  normVarianceBound 24804 (mW 12402) / (3*inputVarianceMean 24804 (mW 12402))^2

end BstLean.Part268.WorldRow12402
namespace BstLean.Part268.WorldRow12403
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12403 = 212492498470295 := by
  have hu : mW 12403 ≤ 212492498470295 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12403 ≤ 212492498470294 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12403)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24806 ^ 2)
    ((25000000000000000000/3896517368247420553674341))
    ((5000000000000000000/779272057722948212800003)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24806) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24806 : ℝ)^2 / (mW 12403 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1043003/500000000000))/2) * ((1-firstRatio 24806) * √(1-firstRatio 24806) *
      sixthConstant (e1CovarianceRatio 24806 (mW 12403) (1/10^6) rowEps))) /
    (712/10000 - 24806*(1+1/10^6)*((1043003/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24806 (mW 12403) /
    ((1/10^5) * ((mW 12403 : ℝ)*24806*((mW 12403 : ℝ)+24806+1)))^2 +
  8*(mW 12403 : ℝ)*24806*(24806+2)*(24806+3) /
    ((1/1000)*((mW 12403 : ℝ)*24806*(24806+2)))^2 +
  covarianceVarianceBound 24806 (mW 12403) /
    ((1/1000)*covarianceMeanBound 24806 (mW 12403))^2 +
  normVarianceBound 24806 (mW 12403) / (3*inputVarianceMean 24806 (mW 12403))^2

end BstLean.Part268.WorldRow12403
namespace BstLean.Part268.WorldRow12404
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12404 = 212552467727869 := by
  have hu : mW 12404 ≤ 212552467727869 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12404 ≤ 212552467727868 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12404)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24808 ^ 2)
    ((6250000000000000000/974207881878194883249547))
    ((25000000000000000000/3896674447880100043323861)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24808) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24808 : ℝ)^2 / (mW 12404 : ℝ)) * (1 + 1/10^6)^2 *
    √(((521459/250000000000))/2) * ((1-firstRatio 24808) * √(1-firstRatio 24808) *
      sixthConstant (e1CovarianceRatio 24808 (mW 12404) (1/10^6) rowEps))) /
    (712/10000 - 24808*(1+1/10^6)*((521459/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24808 (mW 12404) /
    ((1/10^5) * ((mW 12404 : ℝ)*24808*((mW 12404 : ℝ)+24808+1)))^2 +
  8*(mW 12404 : ℝ)*24808*(24808+2)*(24808+3) /
    ((1/1000)*((mW 12404 : ℝ)*24808*(24808+2)))^2 +
  covarianceVarianceBound 24808 (mW 12404) /
    ((1/1000)*covarianceMeanBound 24808 (mW 12404))^2 +
  normVarianceBound 24808 (mW 12404) / (3*inputVarianceMean 24808 (mW 12404))^2

end BstLean.Part268.WorldRow12404
namespace BstLean.Part268.WorldRow12405
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12405 = 212612449073338 := by
  have hu : mW 12405 ≤ 212612449073338 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12405 ≤ 212612449073337 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12405)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24810 ^ 2)
    ((5000000000000000000/779429137355627702464407))
    ((25000000000000000000/3896988607145459022647707)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24810) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24810 : ℝ)^2 / (mW 12405 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1042833/500000000000))/2) * ((1-firstRatio 24810) * √(1-firstRatio 24810) *
      sixthConstant (e1CovarianceRatio 24810 (mW 12405) (1/10^6) rowEps))) /
    (712/10000 - 24810*(1+1/10^6)*((1042833/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24810 (mW 12405) /
    ((1/10^5) * ((mW 12405 : ℝ)*24810*((mW 12405 : ℝ)+24810+1)))^2 +
  8*(mW 12405 : ℝ)*24810*(24810+2)*(24810+3) /
    ((1/1000)*((mW 12405 : ℝ)*24810*(24810+2)))^2 +
  covarianceVarianceBound 24810 (mW 12405) /
    ((1/1000)*covarianceMeanBound 24810 (mW 12405))^2 +
  normVarianceBound 24810 (mW 12405) / (3*inputVarianceMean 24810 (mW 12405))^2

end BstLean.Part268.WorldRow12405
namespace BstLean.Part268.WorldRow12406
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12406 = 212672442508164 := by
  have hu : mW 12406 ≤ 212672442508164 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12406 ≤ 212672442508163 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12406)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24812 ^ 2)
    ((12500000000000000000/1948729923021748745822941))
    ((25000000000000000000/3897302766410818001971553)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24812) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24812 : ℝ)^2 / (mW 12406 : ℝ)) * (1 + 1/10^6)^2 *
    √(((260687/125000000000))/2) * ((1-firstRatio 24812) * √(1-firstRatio 24812) *
      sixthConstant (e1CovarianceRatio 24812 (mW 12406) (1/10^6) rowEps))) /
    (712/10000 - 24812*(1+1/10^6)*((260687/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24812 (mW 12406) /
    ((1/10^5) * ((mW 12406 : ℝ)*24812*((mW 12406 : ℝ)+24812+1)))^2 +
  8*(mW 12406 : ℝ)*24812*(24812+2)*(24812+3) /
    ((1/1000)*((mW 12406 : ℝ)*24812*(24812+2)))^2 +
  covarianceVarianceBound 24812 (mW 12406) /
    ((1/1000)*covarianceMeanBound 24812 (mW 12406))^2 +
  normVarianceBound 24812 (mW 12406) / (3*inputVarianceMean 24812 (mW 12406))^2

end BstLean.Part268.WorldRow12406
namespace BstLean.Part268.WorldRow12407
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12407 = 212732448033809 := by
  have hu : mW 12407 ≤ 212732448033809 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12407 ≤ 212732448033808 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12407)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24814 ^ 2)
    ((25000000000000000000/3897774005308856470969729))
    ((25000000000000000000/3897616925676176981295399)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24814) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24814 : ℝ)^2 / (mW 12407 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1042663/500000000000))/2) * ((1-firstRatio 24814) * √(1-firstRatio 24814) *
      sixthConstant (e1CovarianceRatio 24814 (mW 12407) (1/10^6) rowEps))) /
    (712/10000 - 24814*(1+1/10^6)*((1042663/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24814 (mW 12407) /
    ((1/10^5) * ((mW 12407 : ℝ)*24814*((mW 12407 : ℝ)+24814+1)))^2 +
  8*(mW 12407 : ℝ)*24814*(24814+2)*(24814+3) /
    ((1/1000)*((mW 12407 : ℝ)*24814*(24814+2)))^2 +
  covarianceVarianceBound 24814 (mW 12407) /
    ((1/1000)*covarianceMeanBound 24814 (mW 12407))^2 +
  normVarianceBound 24814 (mW 12407) / (3*inputVarianceMean 24814 (mW 12407))^2

end BstLean.Part268.WorldRow12407
namespace BstLean.Part268.WorldRow12408
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12408 = 212792465651734 := by
  have hu : mW 12408 ≤ 212792465651734 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12408 ≤ 212792465651733 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12408)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24816 ^ 2)
    ((3125000000000000000/487261020571776931286697))
    ((5000000000000000000/779586216988307192123849)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24816) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24816 : ℝ)^2 / (mW 12408 : ℝ)) * (1 + 1/10^6)^2 *
    √(((521289/250000000000))/2) * ((1-firstRatio 24816) * √(1-firstRatio 24816) *
      sixthConstant (e1CovarianceRatio 24816 (mW 12408) (1/10^6) rowEps))) /
    (712/10000 - 24816*(1+1/10^6)*((521289/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24816 (mW 12408) /
    ((1/10^5) * ((mW 12408 : ℝ)*24816*((mW 12408 : ℝ)+24816+1)))^2 +
  8*(mW 12408 : ℝ)*24816*(24816+2)*(24816+3) /
    ((1/1000)*((mW 12408 : ℝ)*24816*(24816+2)))^2 +
  covarianceVarianceBound 24816 (mW 12408) /
    ((1/1000)*covarianceMeanBound 24816 (mW 12408))^2 +
  normVarianceBound 24816 (mW 12408) / (3*inputVarianceMean 24816 (mW 12408))^2

end BstLean.Part268.WorldRow12408
namespace BstLean.Part268.WorldRow12409
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12409 = 212852495363403 := by
  have hu : mW 12409 ≤ 212852495363403 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12409 ≤ 212852495363402 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12409)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24818 ^ 2)
    ((25000000000000000000/3898402323839574429617423))
    ((25000000000000000000/3898245244206894939943091)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24818) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24818 : ℝ)^2 / (mW 12409 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2084987/1000000000000))/2) * ((1-firstRatio 24818) * √(1-firstRatio 24818) *
      sixthConstant (e1CovarianceRatio 24818 (mW 12409) (1/10^6) rowEps))) /
    (712/10000 - 24818*(1+1/10^6)*((2084987/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24818 (mW 12409) /
    ((1/10^5) * ((mW 12409 : ℝ)*24818*((mW 12409 : ℝ)+24818+1)))^2 +
  8*(mW 12409 : ℝ)*24818*(24818+2)*(24818+3) /
    ((1/1000)*((mW 12409 : ℝ)*24818*(24818+2)))^2 +
  covarianceVarianceBound 24818 (mW 12409) /
    ((1/1000)*covarianceMeanBound 24818 (mW 12409))^2 +
  normVarianceBound 24818 (mW 12409) / (3*inputVarianceMean 24818 (mW 12409))^2

end BstLean.Part268.WorldRow12409
namespace BstLean.Part268.WorldRow12410
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12410 = 212912537170277 := by
  have hu : mW 12410 ≤ 212912537170277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12410 ≤ 212912537170276 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12410)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24820 ^ 2)
    ((2500000000000000000/389871648310493340894127))
    ((25000000000000000000/3898559403472253919266937)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24820) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24820 : ℝ)^2 / (mW 12410 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2084817/1000000000000))/2) * ((1-firstRatio 24820) * √(1-firstRatio 24820) *
      sixthConstant (e1CovarianceRatio 24820 (mW 12410) (1/10^6) rowEps))) /
    (712/10000 - 24820*(1+1/10^6)*((2084817/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24820 (mW 12410) /
    ((1/10^5) * ((mW 12410 : ℝ)*24820*((mW 12410 : ℝ)+24820+1)))^2 +
  8*(mW 12410 : ℝ)*24820*(24820+2)*(24820+3) /
    ((1/1000)*((mW 12410 : ℝ)*24820*(24820+2)))^2 +
  covarianceVarianceBound 24820 (mW 12410) /
    ((1/1000)*covarianceMeanBound 24820 (mW 12410))^2 +
  normVarianceBound 24820 (mW 12410) / (3*inputVarianceMean 24820 (mW 12410))^2

end BstLean.Part268.WorldRow12410
namespace BstLean.Part268.WorldRow12411
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12411 = 212972591073817 := by
  have hu : mW 12411 ≤ 212972591073817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12411 ≤ 212972591073816 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12411)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24822 ^ 2)
    ((25000000000000000000/3899030642370292388265117))
    ((25000000000000000000/3898873562737612898590783)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24822) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24822 : ℝ)^2 / (mW 12411 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2084647/1000000000000))/2) * ((1-firstRatio 24822) * √(1-firstRatio 24822) *
      sixthConstant (e1CovarianceRatio 24822 (mW 12411) (1/10^6) rowEps))) /
    (712/10000 - 24822*(1+1/10^6)*((2084647/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24822 (mW 12411) /
    ((1/10^5) * ((mW 12411 : ℝ)*24822*((mW 12411 : ℝ)+24822+1)))^2 +
  8*(mW 12411 : ℝ)*24822*(24822+2)*(24822+3) /
    ((1/1000)*((mW 12411 : ℝ)*24822*(24822+2)))^2 +
  covarianceVarianceBound 24822 (mW 12411) /
    ((1/1000)*covarianceMeanBound 24822 (mW 12411))^2 +
  normVarianceBound 24822 (mW 12411) / (3*inputVarianceMean 24822 (mW 12411))^2

end BstLean.Part268.WorldRow12411
namespace BstLean.Part268.WorldRow12412
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12412 = 213032657075487 := by
  have hu : mW 12412 ≤ 213032657075487 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12412 ≤ 213032657075486 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12412)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24824 ^ 2)
    ((6250000000000000000/974836200408912841897241))
    ((25000000000000000000/3899187722002971877914629)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24824) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24824 : ℝ)^2 / (mW 12412 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2084477/1000000000000))/2) * ((1-firstRatio 24824) * √(1-firstRatio 24824) *
      sixthConstant (e1CovarianceRatio 24824 (mW 12412) (1/10^6) rowEps))) /
    (712/10000 - 24824*(1+1/10^6)*((2084477/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24824 (mW 12412) /
    ((1/10^5) * ((mW 12412 : ℝ)*24824*((mW 12412 : ℝ)+24824+1)))^2 +
  8*(mW 12412 : ℝ)*24824*(24824+2)*(24824+3) /
    ((1/1000)*((mW 12412 : ℝ)*24824*(24824+2)))^2 +
  covarianceVarianceBound 24824 (mW 12412) /
    ((1/1000)*covarianceMeanBound 24824 (mW 12412))^2 +
  normVarianceBound 24824 (mW 12412) / (3*inputVarianceMean 24824 (mW 12412))^2

end BstLean.Part268.WorldRow12412
namespace BstLean.Part268.WorldRow12413
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12413 = 213092735176748 := by
  have hu : mW 12413 ≤ 213092735176748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12413 ≤ 213092735176747 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12413)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24826 ^ 2)
    ((25000000000000000000/3899658960901010346912811))
    ((1000000000000000000/155980075250733234289539)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24826) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24826 : ℝ)^2 / (mW 12413 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2084307/1000000000000))/2) * ((1-firstRatio 24826) * √(1-firstRatio 24826) *
      sixthConstant (e1CovarianceRatio 24826 (mW 12413) (1/10^6) rowEps))) /
    (712/10000 - 24826*(1+1/10^6)*((2084307/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24826 (mW 12413) /
    ((1/10^5) * ((mW 12413 : ℝ)*24826*((mW 12413 : ℝ)+24826+1)))^2 +
  8*(mW 12413 : ℝ)*24826*(24826+2)*(24826+3) /
    ((1/1000)*((mW 12413 : ℝ)*24826*(24826+2)))^2 +
  covarianceVarianceBound 24826 (mW 12413) /
    ((1/1000)*covarianceMeanBound 24826 (mW 12413))^2 +
  normVarianceBound 24826 (mW 12413) / (3*inputVarianceMean 24826 (mW 12413))^2

end BstLean.Part268.WorldRow12413
namespace BstLean.Part268.WorldRow12414
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12414 = 213152825379063 := by
  have hu : mW 12414 ≤ 213152825379063 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12414 ≤ 213152825379062 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12414)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24828 ^ 2)
    ((12500000000000000000/1949986560083184663118329))
    ((25000000000000000000/3899816040533689836562321)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24828) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24828 : ℝ)^2 / (mW 12414 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1042069/500000000000))/2) * ((1-firstRatio 24828) * √(1-firstRatio 24828) *
      sixthConstant (e1CovarianceRatio 24828 (mW 12414) (1/10^6) rowEps))) /
    (712/10000 - 24828*(1+1/10^6)*((1042069/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24828 (mW 12414) /
    ((1/10^5) * ((mW 12414 : ℝ)*24828*((mW 12414 : ℝ)+24828+1)))^2 +
  8*(mW 12414 : ℝ)*24828*(24828+2)*(24828+3) /
    ((1/1000)*((mW 12414 : ℝ)*24828*(24828+2)))^2 +
  covarianceVarianceBound 24828 (mW 12414) /
    ((1/1000)*covarianceMeanBound 24828 (mW 12414))^2 +
  normVarianceBound 24828 (mW 12414) / (3*inputVarianceMean 24828 (mW 12414))^2

end BstLean.Part268.WorldRow12414
namespace BstLean.Part268.WorldRow12415
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12415 = 213212927683894 := by
  have hu : mW 12415 ≤ 213212927683894 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12415 ≤ 213212927683893 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12415)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24830 ^ 2)
    ((5000000000000000000/780057455886345661112101))
    ((25000000000000000000/3900130199799048815886167)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24830) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24830 : ℝ)^2 / (mW 12415 : ℝ)) * (1 + 1/10^6)^2 *
    √(((16281/7812500000))/2) * ((1-firstRatio 24830) * √(1-firstRatio 24830) *
      sixthConstant (e1CovarianceRatio 24830 (mW 12415) (1/10^6) rowEps))) /
    (712/10000 - 24830*(1+1/10^6)*((16281/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24830 (mW 12415) /
    ((1/10^5) * ((mW 12415 : ℝ)*24830*((mW 12415 : ℝ)+24830+1)))^2 +
  8*(mW 12415 : ℝ)*24830*(24830+2)*(24830+3) /
    ((1/1000)*((mW 12415 : ℝ)*24830*(24830+2)))^2 +
  covarianceVarianceBound 24830 (mW 12415) /
    ((1/1000)*covarianceMeanBound 24830 (mW 12415))^2 +
  normVarianceBound 24830 (mW 12415) / (3*inputVarianceMean 24830 (mW 12415))^2

end BstLean.Part268.WorldRow12415
namespace BstLean.Part268.WorldRow12416
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12416 = 213273042092703 := by
  have hu : mW 12416 ≤ 213273042092703 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12416 ≤ 213273042092702 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12416)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24832 ^ 2)
    ((195312500000000000/30473448739820994413159))
    ((25000000000000000000/3900444359064407795210013)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24832) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24832 : ℝ)^2 / (mW 12416 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1041899/500000000000))/2) * ((1-firstRatio 24832) * √(1-firstRatio 24832) *
      sixthConstant (e1CovarianceRatio 24832 (mW 12416) (1/10^6) rowEps))) /
    (712/10000 - 24832*(1+1/10^6)*((1041899/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24832 (mW 12416) /
    ((1/10^5) * ((mW 12416 : ℝ)*24832*((mW 12416 : ℝ)+24832+1)))^2 +
  8*(mW 12416 : ℝ)*24832*(24832+2)*(24832+3) /
    ((1/1000)*((mW 12416 : ℝ)*24832*(24832+2)))^2 +
  covarianceVarianceBound 24832 (mW 12416) /
    ((1/1000)*covarianceMeanBound 24832 (mW 12416))^2 +
  normVarianceBound 24832 (mW 12416) / (3*inputVarianceMean 24832 (mW 12416))^2

end BstLean.Part268.WorldRow12416
namespace BstLean.Part268.WorldRow12417
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12417 = 213333168606953 := by
  have hu : mW 12417 ≤ 213333168606953 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12417 ≤ 213333168606952 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12417)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24834 ^ 2)
    ((25000000000000000000/3900915597962446264208199))
    ((25000000000000000000/3900758518329766774533859)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24834) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24834 : ℝ)^2 / (mW 12417 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2083629/1000000000000))/2) * ((1-firstRatio 24834) * √(1-firstRatio 24834) *
      sixthConstant (e1CovarianceRatio 24834 (mW 12417) (1/10^6) rowEps))) /
    (712/10000 - 24834*(1+1/10^6)*((2083629/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24834 (mW 12417) /
    ((1/10^5) * ((mW 12417 : ℝ)*24834*((mW 12417 : ℝ)+24834+1)))^2 +
  8*(mW 12417 : ℝ)*24834*(24834+2)*(24834+3) /
    ((1/1000)*((mW 12417 : ℝ)*24834*(24834+2)))^2 +
  covarianceVarianceBound 24834 (mW 12417) /
    ((1/1000)*covarianceMeanBound 24834 (mW 12417))^2 +
  normVarianceBound 24834 (mW 12417) / (3*inputVarianceMean 24834 (mW 12417))^2

end BstLean.Part268.WorldRow12417
namespace BstLean.Part268.WorldRow12418
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12418 = 213393307228106 := by
  have hu : mW 12418 ≤ 213393307228106 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12418 ≤ 213393307228105 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12418)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24836 ^ 2)
    ((12500000000000000000/1950614878613902621766023))
    ((5000000000000000000/780214535519025150771541)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24836) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24836 : ℝ)^2 / (mW 12418 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2083459/1000000000000))/2) * ((1-firstRatio 24836) * √(1-firstRatio 24836) *
      sixthConstant (e1CovarianceRatio 24836 (mW 12418) (1/10^6) rowEps))) /
    (712/10000 - 24836*(1+1/10^6)*((2083459/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24836 (mW 12418) /
    ((1/10^5) * ((mW 12418 : ℝ)*24836*((mW 12418 : ℝ)+24836+1)))^2 +
  8*(mW 12418 : ℝ)*24836*(24836+2)*(24836+3) /
    ((1/1000)*((mW 12418 : ℝ)*24836*(24836+2)))^2 +
  covarianceVarianceBound 24836 (mW 12418) /
    ((1/1000)*covarianceMeanBound 24836 (mW 12418))^2 +
  normVarianceBound 24836 (mW 12418) / (3*inputVarianceMean 24836 (mW 12418))^2

end BstLean.Part268.WorldRow12418
namespace BstLean.Part268.WorldRow12419
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12419 = 213453457957625 := by
  have hu : mW 12419 ≤ 213453457957625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12419 ≤ 213453457957624 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12419)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24838 ^ 2)
    ((25000000000000000000/3901543916493164222855893))
    ((25000000000000000000/3901386836860484733181551)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24838) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24838 : ℝ)^2 / (mW 12419 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2083289/1000000000000))/2) * ((1-firstRatio 24838) * √(1-firstRatio 24838) *
      sixthConstant (e1CovarianceRatio 24838 (mW 12419) (1/10^6) rowEps))) /
    (712/10000 - 24838*(1+1/10^6)*((2083289/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24838 (mW 12419) /
    ((1/10^5) * ((mW 12419 : ℝ)*24838*((mW 12419 : ℝ)+24838+1)))^2 +
  8*(mW 12419 : ℝ)*24838*(24838+2)*(24838+3) /
    ((1/1000)*((mW 12419 : ℝ)*24838*(24838+2)))^2 +
  covarianceVarianceBound 24838 (mW 12419) /
    ((1/1000)*covarianceMeanBound 24838 (mW 12419))^2 +
  normVarianceBound 24838 (mW 12419) / (3*inputVarianceMean 24838 (mW 12419))^2

end BstLean.Part268.WorldRow12419
namespace BstLean.Part268.WorldRow12420
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12420 = 213513620796973 := by
  have hu : mW 12420 ≤ 213513620796973 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12420 ≤ 213513620796972 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12420)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24840 ^ 2)
    ((1250000000000000000/195092903787926160108987))
    ((25000000000000000000/3901700996125843712505397)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24840) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24840 : ℝ)^2 / (mW 12420 : ℝ)) * (1 + 1/10^6)^2 *
    √(((26039/12500000000))/2) * ((1-firstRatio 24840) * √(1-firstRatio 24840) *
      sixthConstant (e1CovarianceRatio 24840 (mW 12420) (1/10^6) rowEps))) /
    (712/10000 - 24840*(1+1/10^6)*((26039/12500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24840 (mW 12420) /
    ((1/10^5) * ((mW 12420 : ℝ)*24840*((mW 12420 : ℝ)+24840+1)))^2 +
  8*(mW 12420 : ℝ)*24840*(24840+2)*(24840+3) /
    ((1/1000)*((mW 12420 : ℝ)*24840*(24840+2)))^2 +
  covarianceVarianceBound 24840 (mW 12420) /
    ((1/1000)*covarianceMeanBound 24840 (mW 12420))^2 +
  normVarianceBound 24840 (mW 12420) / (3*inputVarianceMean 24840 (mW 12420))^2

end BstLean.Part268.WorldRow12420
namespace BstLean.Part268.WorldRow12421
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12421 = 213573795747612 := by
  have hu : mW 12421 ≤ 213573795747612 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12421 ≤ 213573795747611 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12421)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24842 ^ 2)
    ((25000000000000000000/3902172235023882181503587))
    ((25000000000000000000/3902015155391202691829243)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24842) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24842 : ℝ)^2 / (mW 12421 : ℝ)) * (1 + 1/10^6)^2 *
    √(((41659/20000000000))/2) * ((1-firstRatio 24842) * √(1-firstRatio 24842) *
      sixthConstant (e1CovarianceRatio 24842 (mW 12421) (1/10^6) rowEps))) /
    (712/10000 - 24842*(1+1/10^6)*((41659/20000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24842 (mW 12421) /
    ((1/10^5) * ((mW 12421 : ℝ)*24842*((mW 12421 : ℝ)+24842+1)))^2 +
  8*(mW 12421 : ℝ)*24842*(24842+2)*(24842+3) /
    ((1/1000)*((mW 12421 : ℝ)*24842*(24842+2)))^2 +
  covarianceVarianceBound 24842 (mW 12421) /
    ((1/1000)*covarianceMeanBound 24842 (mW 12421))^2 +
  normVarianceBound 24842 (mW 12421) / (3*inputVarianceMean 24842 (mW 12421))^2

end BstLean.Part268.WorldRow12421
namespace BstLean.Part268.WorldRow12422
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12422 = 213633982811005 := by
  have hu : mW 12422 ≤ 213633982811005 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12422 ≤ 213633982811004 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12422)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24844 ^ 2)
    ((12500000000000000000/1951243197144620580413717))
    ((25000000000000000000/3902329314656561671153089)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24844) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24844 : ℝ)^2 / (mW 12422 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2082781/1000000000000))/2) * ((1-firstRatio 24844) * √(1-firstRatio 24844) *
      sixthConstant (e1CovarianceRatio 24844 (mW 12422) (1/10^6) rowEps))) /
    (712/10000 - 24844*(1+1/10^6)*((2082781/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24844 (mW 12422) /
    ((1/10^5) * ((mW 12422 : ℝ)*24844*((mW 12422 : ℝ)+24844+1)))^2 +
  8*(mW 12422 : ℝ)*24844*(24844+2)*(24844+3) /
    ((1/1000)*((mW 12422 : ℝ)*24844*(24844+2)))^2 +
  covarianceVarianceBound 24844 (mW 12422) /
    ((1/1000)*covarianceMeanBound 24844 (mW 12422))^2 +
  normVarianceBound 24844 (mW 12422) / (3*inputVarianceMean 24844 (mW 12422))^2

end BstLean.Part268.WorldRow12422
namespace BstLean.Part268.WorldRow12423
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12423 = 213694181988615 := by
  have hu : mW 12423 ≤ 213694181988615 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12423 ≤ 213694181988614 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12423)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24846 ^ 2)
    ((25000000000000000000/3902800553554600140151281))
    ((5000000000000000000/780528694784384130095387)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24846) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24846 : ℝ)^2 / (mW 12423 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2082611/1000000000000))/2) * ((1-firstRatio 24846) * √(1-firstRatio 24846) *
      sixthConstant (e1CovarianceRatio 24846 (mW 12423) (1/10^6) rowEps))) /
    (712/10000 - 24846*(1+1/10^6)*((2082611/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24846 (mW 12423) /
    ((1/10^5) * ((mW 12423 : ℝ)*24846*((mW 12423 : ℝ)+24846+1)))^2 +
  8*(mW 12423 : ℝ)*24846*(24846+2)*(24846+3) /
    ((1/1000)*((mW 12423 : ℝ)*24846*(24846+2)))^2 +
  covarianceVarianceBound 24846 (mW 12423) /
    ((1/1000)*covarianceMeanBound 24846 (mW 12423))^2 +
  normVarianceBound 24846 (mW 12423) / (3*inputVarianceMean 24846 (mW 12423))^2

end BstLean.Part268.WorldRow12423
namespace BstLean.Part268.WorldRow12424
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12424 = 213754393281904 := by
  have hu : mW 12424 ≤ 213754393281904 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12424 ≤ 213754393281903 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12424)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 24848 ^ 2)
    ((3125000000000000000/487889339102494889934391))
    ((25000000000000000000/3902957633187279629800781)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 24848) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (24848 : ℝ)^2 / (mW 12424 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1041221/500000000000))/2) * ((1-firstRatio 24848) * √(1-firstRatio 24848) *
      sixthConstant (e1CovarianceRatio 24848 (mW 12424) (1/10^6) rowEps))) /
    (712/10000 - 24848*(1+1/10^6)*((1041221/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 24848 (mW 12424) /
    ((1/10^5) * ((mW 12424 : ℝ)*24848*((mW 12424 : ℝ)+24848+1)))^2 +
  8*(mW 12424 : ℝ)*24848*(24848+2)*(24848+3) /
    ((1/1000)*((mW 12424 : ℝ)*24848*(24848+2)))^2 +
  covarianceVarianceBound 24848 (mW 12424) /
    ((1/1000)*covarianceMeanBound 24848 (mW 12424))^2 +
  normVarianceBound 24848 (mW 12424) / (3*inputVarianceMean 24848 (mW 12424))^2

end BstLean.Part268.WorldRow12424
