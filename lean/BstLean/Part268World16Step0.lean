import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar16
namespace BstLean.Part268.WorldRow12750
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12750 = 234037605830889 := by
  have hu : mW 12750 ≤ 234037605830889 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12750 ≤ 234037605830888 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12750)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25500 ^ 2)
    ((100000000000000000/16022122533307945516197))
    ((25000000000000000000/4005373553694306889374577)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25500) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25500 : ℝ)^2 / (mW 12750 : ℝ)) * (1 + 1/10^6)^2 *
    √(((12679/6250000000))/2) * ((1-firstRatio 25500) * √(1-firstRatio 25500) *
      sixthConstant (e1CovarianceRatio 25500 (mW 12750) (1/10^6) rowEps))) /
    (712/10000 - 25500*(1+1/10^6)*((12679/6250000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25500 (mW 12750) /
    ((1/10^5) * ((mW 12750 : ℝ)*25500*((mW 12750 : ℝ)+25500+1)))^2 +
  8*(mW 12750 : ℝ)*25500*(25500+2)*(25500+3) /
    ((1/1000)*((mW 12750 : ℝ)*25500*(25500+2)))^2 +
  covarianceVarianceBound 25500 (mW 12750) /
    ((1/1000)*covarianceMeanBound 25500 (mW 12750))^2 +
  normVarianceBound 25500 (mW 12750) / (3*inputVarianceMean 25500 (mW 12750))^2

end BstLean.Part268.WorldRow12750
namespace BstLean.Part268.WorldRow12751
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12751 = 234101857747013 := by
  have hu : mW 12751 ≤ 234101857747013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12751 ≤ 234101857747012 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12751)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25502 ^ 2)
    ((25000000000000000000/4005844792592345358373097))
    ((25000000000000000000/4005687712959665868698423)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25502) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25502 : ℝ)^2 / (mW 12751 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2028479/1000000000000))/2) * ((1-firstRatio 25502) * √(1-firstRatio 25502) *
      sixthConstant (e1CovarianceRatio 25502 (mW 12751) (1/10^6) rowEps))) /
    (712/10000 - 25502*(1+1/10^6)*((2028479/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25502 (mW 12751) /
    ((1/10^5) * ((mW 12751 : ℝ)*25502*((mW 12751 : ℝ)+25502+1)))^2 +
  8*(mW 12751 : ℝ)*25502*(25502+2)*(25502+3) /
    ((1/1000)*((mW 12751 : ℝ)*25502*(25502+2)))^2 +
  covarianceVarianceBound 25502 (mW 12751) /
    ((1/1000)*covarianceMeanBound 25502 (mW 12751))^2 +
  normVarianceBound 25502 (mW 12751) / (3*inputVarianceMean 25502 (mW 12751))^2

end BstLean.Part268.WorldRow12751
namespace BstLean.Part268.WorldRow12752
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12752 = 234166122261798 := by
  have hu : mW 12752 ≤ 234166122261798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12752 ≤ 234166122261797 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12752)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25504 ^ 2)
    ((1562500000000000000/250384934491106521106059))
    ((25000000000000000000/4006001872225024848022269)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25504) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25504 : ℝ)^2 / (mW 12752 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2028319/1000000000000))/2) * ((1-firstRatio 25504) * √(1-firstRatio 25504) *
      sixthConstant (e1CovarianceRatio 25504 (mW 12752) (1/10^6) rowEps))) /
    (712/10000 - 25504*(1+1/10^6)*((2028319/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25504 (mW 12752) /
    ((1/10^5) * ((mW 12752 : ℝ)*25504*((mW 12752 : ℝ)+25504+1)))^2 +
  8*(mW 12752 : ℝ)*25504*(25504+2)*(25504+3) /
    ((1/1000)*((mW 12752 : ℝ)*25504*(25504+2)))^2 +
  covarianceVarianceBound 25504 (mW 12752) /
    ((1/1000)*covarianceMeanBound 25504 (mW 12752))^2 +
  normVarianceBound 25504 (mW 12752) / (3*inputVarianceMean 25504 (mW 12752))^2

end BstLean.Part268.WorldRow12752
namespace BstLean.Part268.WorldRow12753
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12753 = 234230399376728 := by
  have hu : mW 12753 ≤ 234230399376728 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12753 ≤ 234230399376727 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12753)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25506 ^ 2)
    ((25000000000000000000/4006473111123063317020791))
    ((5000000000000000000/801263206298076765469223)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25506) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25506 : ℝ)^2 / (mW 12753 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1014079/500000000000))/2) * ((1-firstRatio 25506) * √(1-firstRatio 25506) *
      sixthConstant (e1CovarianceRatio 25506 (mW 12753) (1/10^6) rowEps))) /
    (712/10000 - 25506*(1+1/10^6)*((1014079/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25506 (mW 12753) /
    ((1/10^5) * ((mW 12753 : ℝ)*25506*((mW 12753 : ℝ)+25506+1)))^2 +
  8*(mW 12753 : ℝ)*25506*(25506+2)*(25506+3) /
    ((1/1000)*((mW 12753 : ℝ)*25506*(25506+2)))^2 +
  covarianceVarianceBound 25506 (mW 12753) /
    ((1/1000)*covarianceMeanBound 25506 (mW 12753))^2 +
  normVarianceBound 25506 (mW 12753) / (3*inputVarianceMean 25506 (mW 12753))^2

end BstLean.Part268.WorldRow12753
namespace BstLean.Part268.WorldRow12754
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12754 = 234294689093284 := by
  have hu : mW 12754 ≤ 234294689093284 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12754 ≤ 234294689093283 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12754)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25508 ^ 2)
    ((12500000000000000000/2003393635194211148172319))
    ((25000000000000000000/4006630190755742806669961)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25508) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25508 : ℝ)^2 / (mW 12754 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2027997/1000000000000))/2) * ((1-firstRatio 25508) * √(1-firstRatio 25508) *
      sixthConstant (e1CovarianceRatio 25508 (mW 12754) (1/10^6) rowEps))) /
    (712/10000 - 25508*(1+1/10^6)*((2027997/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25508 (mW 12754) /
    ((1/10^5) * ((mW 12754 : ℝ)*25508*((mW 12754 : ℝ)+25508+1)))^2 +
  8*(mW 12754 : ℝ)*25508*(25508+2)*(25508+3) /
    ((1/1000)*((mW 12754 : ℝ)*25508*(25508+2)))^2 +
  covarianceVarianceBound 25508 (mW 12754) /
    ((1/1000)*covarianceMeanBound 25508 (mW 12754))^2 +
  normVarianceBound 25508 (mW 12754) / (3*inputVarianceMean 25508 (mW 12754))^2

end BstLean.Part268.WorldRow12754
namespace BstLean.Part268.WorldRow12755
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12755 = 234358991412948 := by
  have hu : mW 12755 ≤ 234358991412948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12755 ≤ 234358991412947 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12755)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25510 ^ 2)
    ((5000000000000000000/801420285930756255133697))
    ((25000000000000000000/4006944350021101785993807)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25510) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25510 : ℝ)^2 / (mW 12755 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2027837/1000000000000))/2) * ((1-firstRatio 25510) * √(1-firstRatio 25510) *
      sixthConstant (e1CovarianceRatio 25510 (mW 12755) (1/10^6) rowEps))) /
    (712/10000 - 25510*(1+1/10^6)*((2027837/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25510 (mW 12755) /
    ((1/10^5) * ((mW 12755 : ℝ)*25510*((mW 12755 : ℝ)+25510+1)))^2 +
  8*(mW 12755 : ℝ)*25510*(25510+2)*(25510+3) /
    ((1/1000)*((mW 12755 : ℝ)*25510*(25510+2)))^2 +
  covarianceVarianceBound 25510 (mW 12755) /
    ((1/1000)*covarianceMeanBound 25510 (mW 12755))^2 +
  normVarianceBound 25510 (mW 12755) / (3*inputVarianceMean 25510 (mW 12755))^2

end BstLean.Part268.WorldRow12755
namespace BstLean.Part268.WorldRow12756
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12756 = 234423306337204 := by
  have hu : mW 12756 ≤ 234423306337204 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12756 ≤ 234423306337203 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12756)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25512 ^ 2)
    ((6250000000000000000/1001853897229785063748083))
    ((25000000000000000000/4007258509286460765317653)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25512) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25512 : ℝ)^2 / (mW 12756 : ℝ)) * (1 + 1/10^6)^2 *
    √(((506919/250000000000))/2) * ((1-firstRatio 25512) * √(1-firstRatio 25512) *
      sixthConstant (e1CovarianceRatio 25512 (mW 12756) (1/10^6) rowEps))) /
    (712/10000 - 25512*(1+1/10^6)*((506919/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25512 (mW 12756) /
    ((1/10^5) * ((mW 12756 : ℝ)*25512*((mW 12756 : ℝ)+25512+1)))^2 +
  8*(mW 12756 : ℝ)*25512*(25512+2)*(25512+3) /
    ((1/1000)*((mW 12756 : ℝ)*25512*(25512+2)))^2 +
  covarianceVarianceBound 25512 (mW 12756) /
    ((1/1000)*covarianceMeanBound 25512 (mW 12756))^2 +
  normVarianceBound 25512 (mW 12756) / (3*inputVarianceMean 25512 (mW 12756))^2

end BstLean.Part268.WorldRow12756
namespace BstLean.Part268.WorldRow12757
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12757 = 234487633867532 := by
  have hu : mW 12757 ≤ 234487633867532 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12757 ≤ 234487633867531 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12757)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25514 ^ 2)
    ((25000000000000000000/4007729748184499234316179))
    ((25000000000000000000/4007572668551819744641499)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25514) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25514 : ℝ)^2 / (mW 12757 : ℝ)) * (1 + 1/10^6)^2 *
    √(((405503/200000000000))/2) * ((1-firstRatio 25514) * √(1-firstRatio 25514) *
      sixthConstant (e1CovarianceRatio 25514 (mW 12757) (1/10^6) rowEps))) /
    (712/10000 - 25514*(1+1/10^6)*((405503/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25514 (mW 12757) /
    ((1/10^5) * ((mW 12757 : ℝ)*25514*((mW 12757 : ℝ)+25514+1)))^2 +
  8*(mW 12757 : ℝ)*25514*(25514+2)*(25514+3) /
    ((1/1000)*((mW 12757 : ℝ)*25514*(25514+2)))^2 +
  covarianceVarianceBound 25514 (mW 12757) /
    ((1/1000)*covarianceMeanBound 25514 (mW 12757))^2 +
  normVarianceBound 25514 (mW 12757) / (3*inputVarianceMean 25514 (mW 12757))^2

end BstLean.Part268.WorldRow12757
namespace BstLean.Part268.WorldRow12758
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12758 = 234551974005415 := by
  have hu : mW 12758 ≤ 234551974005415 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12758 ≤ 234551974005414 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12758)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25516 ^ 2)
    ((12500000000000000000/2004021953724929106820013))
    ((5000000000000000000/801577365563435744793069)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25516) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25516 : ℝ)^2 / (mW 12758 : ℝ)) * (1 + 1/10^6)^2 *
    √(((405471/200000000000))/2) * ((1-firstRatio 25516) * √(1-firstRatio 25516) *
      sixthConstant (e1CovarianceRatio 25516 (mW 12758) (1/10^6) rowEps))) /
    (712/10000 - 25516*(1+1/10^6)*((405471/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25516 (mW 12758) /
    ((1/10^5) * ((mW 12758 : ℝ)*25516*((mW 12758 : ℝ)+25516+1)))^2 +
  8*(mW 12758 : ℝ)*25516*(25516+2)*(25516+3) /
    ((1/1000)*((mW 12758 : ℝ)*25516*(25516+2)))^2 +
  covarianceVarianceBound 25516 (mW 12758) /
    ((1/1000)*covarianceMeanBound 25516 (mW 12758))^2 +
  normVarianceBound 25516 (mW 12758) / (3*inputVarianceMean 25516 (mW 12758))^2

end BstLean.Part268.WorldRow12758
namespace BstLean.Part268.WorldRow12759
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12759 = 234616326752337 := by
  have hu : mW 12759 ≤ 234616326752337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12759 ≤ 234616326752336 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12759)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25518 ^ 2)
    ((25000000000000000000/4008358066715217192963873))
    ((25000000000000000000/4008200987082537703289191)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25518) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25518 : ℝ)^2 / (mW 12759 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1013597/500000000000))/2) * ((1-firstRatio 25518) * √(1-firstRatio 25518) *
      sixthConstant (e1CovarianceRatio 25518 (mW 12759) (1/10^6) rowEps))) /
    (712/10000 - 25518*(1+1/10^6)*((1013597/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25518 (mW 12759) /
    ((1/10^5) * ((mW 12759 : ℝ)*25518*((mW 12759 : ℝ)+25518+1)))^2 +
  8*(mW 12759 : ℝ)*25518*(25518+2)*(25518+3) /
    ((1/1000)*((mW 12759 : ℝ)*25518*(25518+2)))^2 +
  covarianceVarianceBound 25518 (mW 12759) /
    ((1/1000)*covarianceMeanBound 25518 (mW 12759))^2 +
  normVarianceBound 25518 (mW 12759) / (3*inputVarianceMean 25518 (mW 12759))^2

end BstLean.Part268.WorldRow12759
namespace BstLean.Part268.WorldRow12760
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12760 = 234680692109779 := by
  have hu : mW 12760 ≤ 234680692109779 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12760 ≤ 234680692109778 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12760)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25520 ^ 2)
    ((625000000000000000/100216805649514404307193))
    ((25000000000000000000/4008515146347896682613037)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25520) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25520 : ℝ)^2 / (mW 12760 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1013517/500000000000))/2) * ((1-firstRatio 25520) * √(1-firstRatio 25520) *
      sixthConstant (e1CovarianceRatio 25520 (mW 12760) (1/10^6) rowEps))) /
    (712/10000 - 25520*(1+1/10^6)*((1013517/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25520 (mW 12760) /
    ((1/10^5) * ((mW 12760 : ℝ)*25520*((mW 12760 : ℝ)+25520+1)))^2 +
  8*(mW 12760 : ℝ)*25520*(25520+2)*(25520+3) /
    ((1/1000)*((mW 12760 : ℝ)*25520*(25520+2)))^2 +
  covarianceVarianceBound 25520 (mW 12760) /
    ((1/1000)*covarianceMeanBound 25520 (mW 12760))^2 +
  normVarianceBound 25520 (mW 12760) / (3*inputVarianceMean 25520 (mW 12760))^2

end BstLean.Part268.WorldRow12760
namespace BstLean.Part268.WorldRow12761
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12761 = 234745070079223 := by
  have hu : mW 12761 ≤ 234745070079223 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12761 ≤ 234745070079222 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12761)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25522 ^ 2)
    ((25000000000000000000/4008986385245935151611567))
    ((25000000000000000000/4008829305613255661936883)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25522) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25522 : ℝ)^2 / (mW 12761 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2026873/1000000000000))/2) * ((1-firstRatio 25522) * √(1-firstRatio 25522) *
      sixthConstant (e1CovarianceRatio 25522 (mW 12761) (1/10^6) rowEps))) /
    (712/10000 - 25522*(1+1/10^6)*((2026873/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25522 (mW 12761) /
    ((1/10^5) * ((mW 12761 : ℝ)*25522*((mW 12761 : ℝ)+25522+1)))^2 +
  8*(mW 12761 : ℝ)*25522*(25522+2)*(25522+3) /
    ((1/1000)*((mW 12761 : ℝ)*25522*(25522+2)))^2 +
  covarianceVarianceBound 25522 (mW 12761) /
    ((1/1000)*covarianceMeanBound 25522 (mW 12761))^2 +
  normVarianceBound 25522 (mW 12761) / (3*inputVarianceMean 25522 (mW 12761))^2

end BstLean.Part268.WorldRow12761
namespace BstLean.Part268.WorldRow12762
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12762 = 234809460662154 := by
  have hu : mW 12762 ≤ 234809460662154 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12762 ≤ 234809460662153 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12762)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25524 ^ 2)
    ((12500000000000000000/2004650272255647065467707))
    ((25000000000000000000/4009143464878614641260729)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25524) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25524 : ℝ)^2 / (mW 12762 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2026713/1000000000000))/2) * ((1-firstRatio 25524) * √(1-firstRatio 25524) *
      sixthConstant (e1CovarianceRatio 25524 (mW 12762) (1/10^6) rowEps))) /
    (712/10000 - 25524*(1+1/10^6)*((2026713/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25524 (mW 12762) /
    ((1/10^5) * ((mW 12762 : ℝ)*25524*((mW 12762 : ℝ)+25524+1)))^2 +
  8*(mW 12762 : ℝ)*25524*(25524+2)*(25524+3) /
    ((1/1000)*((mW 12762 : ℝ)*25524*(25524+2)))^2 +
  covarianceVarianceBound 25524 (mW 12762) /
    ((1/1000)*covarianceMeanBound 25524 (mW 12762))^2 +
  normVarianceBound 25524 (mW 12762) / (3*inputVarianceMean 25524 (mW 12762))^2

end BstLean.Part268.WorldRow12762
namespace BstLean.Part268.WorldRow12763
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12763 = 234873863860053 := by
  have hu : mW 12763 ≤ 234873863860053 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12763 ≤ 234873863860052 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12763)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25526 ^ 2)
    ((25000000000000000000/4009614703776653110259261))
    ((1000000000000000000/160378304965758944823383)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25526) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25526 : ℝ)^2 / (mW 12763 : ℝ)) * (1 + 1/10^6)^2 *
    √(((253319/125000000000))/2) * ((1-firstRatio 25526) * √(1-firstRatio 25526) *
      sixthConstant (e1CovarianceRatio 25526 (mW 12763) (1/10^6) rowEps))) /
    (712/10000 - 25526*(1+1/10^6)*((253319/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25526 (mW 12763) /
    ((1/10^5) * ((mW 12763 : ℝ)*25526*((mW 12763 : ℝ)+25526+1)))^2 +
  8*(mW 12763 : ℝ)*25526*(25526+2)*(25526+3) /
    ((1/1000)*((mW 12763 : ℝ)*25526*(25526+2)))^2 +
  covarianceVarianceBound 25526 (mW 12763) /
    ((1/1000)*covarianceMeanBound 25526 (mW 12763))^2 +
  normVarianceBound 25526 (mW 12763) / (3*inputVarianceMean 25526 (mW 12763))^2

end BstLean.Part268.WorldRow12763
namespace BstLean.Part268.WorldRow12764
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12764 = 234938279674402 := by
  have hu : mW 12764 ≤ 234938279674402 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12764 ≤ 234938279674401 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12764)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25528 ^ 2)
    ((6250000000000000000/1002482215760503022395777))
    ((25000000000000000000/4009771783409332599908421)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25528) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25528 : ℝ)^2 / (mW 12764 : ℝ)) * (1 + 1/10^6)^2 *
    √(((253299/125000000000))/2) * ((1-firstRatio 25528) * √(1-firstRatio 25528) *
      sixthConstant (e1CovarianceRatio 25528 (mW 12764) (1/10^6) rowEps))) /
    (712/10000 - 25528*(1+1/10^6)*((253299/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25528 (mW 12764) /
    ((1/10^5) * ((mW 12764 : ℝ)*25528*((mW 12764 : ℝ)+25528+1)))^2 +
  8*(mW 12764 : ℝ)*25528*(25528+2)*(25528+3) /
    ((1/1000)*((mW 12764 : ℝ)*25528*(25528+2)))^2 +
  covarianceVarianceBound 25528 (mW 12764) /
    ((1/1000)*covarianceMeanBound 25528 (mW 12764))^2 +
  normVarianceBound 25528 (mW 12764) / (3*inputVarianceMean 25528 (mW 12764))^2

end BstLean.Part268.WorldRow12764
namespace BstLean.Part268.WorldRow12765
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12765 = 235002708106686 := by
  have hu : mW 12765 ≤ 235002708106686 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12765 ≤ 235002708106685 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12765)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25530 ^ 2)
    ((5000000000000000000/802048604461474213781391))
    ((25000000000000000000/4010085942674691579232267)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25530) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25530 : ℝ)^2 / (mW 12765 : ℝ)) * (1 + 1/10^6)^2 *
    √(((253279/125000000000))/2) * ((1-firstRatio 25530) * √(1-firstRatio 25530) *
      sixthConstant (e1CovarianceRatio 25530 (mW 12765) (1/10^6) rowEps))) /
    (712/10000 - 25530*(1+1/10^6)*((253279/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25530 (mW 12765) /
    ((1/10^5) * ((mW 12765 : ℝ)*25530*((mW 12765 : ℝ)+25530+1)))^2 +
  8*(mW 12765 : ℝ)*25530*(25530+2)*(25530+3) /
    ((1/1000)*((mW 12765 : ℝ)*25530*(25530+2)))^2 +
  covarianceVarianceBound 25530 (mW 12765) /
    ((1/1000)*covarianceMeanBound 25530 (mW 12765))^2 +
  normVarianceBound 25530 (mW 12765) / (3*inputVarianceMean 25530 (mW 12765))^2

end BstLean.Part268.WorldRow12765
namespace BstLean.Part268.WorldRow12766
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12766 = 235067149158387 := by
  have hu : mW 12766 ≤ 235067149158387 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12766 ≤ 235067149158386 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12766)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25532 ^ 2)
    ((12500000000000000000/2005278590786365024115401))
    ((25000000000000000000/4010400101940050558556113)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25532) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25532 : ℝ)^2 / (mW 12766 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2026071/1000000000000))/2) * ((1-firstRatio 25532) * √(1-firstRatio 25532) *
      sixthConstant (e1CovarianceRatio 25532 (mW 12766) (1/10^6) rowEps))) /
    (712/10000 - 25532*(1+1/10^6)*((2026071/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25532 (mW 12766) /
    ((1/10^5) * ((mW 12766 : ℝ)*25532*((mW 12766 : ℝ)+25532+1)))^2 +
  8*(mW 12766 : ℝ)*25532*(25532+2)*(25532+3) /
    ((1/1000)*((mW 12766 : ℝ)*25532*(25532+2)))^2 +
  covarianceVarianceBound 25532 (mW 12766) /
    ((1/1000)*covarianceMeanBound 25532 (mW 12766))^2 +
  normVarianceBound 25532 (mW 12766) / (3*inputVarianceMean 25532 (mW 12766))^2

end BstLean.Part268.WorldRow12766
namespace BstLean.Part268.WorldRow12767
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12767 = 235131602830987 := by
  have hu : mW 12767 ≤ 235131602830987 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12767 ≤ 235131602830986 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12767)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25534 ^ 2)
    ((25000000000000000000/4010871340838089027554649))
    ((25000000000000000000/4010714261205409537879959)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25534) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25534 : ℝ)^2 / (mW 12767 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2025911/1000000000000))/2) * ((1-firstRatio 25534) * √(1-firstRatio 25534) *
      sixthConstant (e1CovarianceRatio 25534 (mW 12767) (1/10^6) rowEps))) /
    (712/10000 - 25534*(1+1/10^6)*((2025911/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25534 (mW 12767) /
    ((1/10^5) * ((mW 12767 : ℝ)*25534*((mW 12767 : ℝ)+25534+1)))^2 +
  8*(mW 12767 : ℝ)*25534*(25534+2)*(25534+3) /
    ((1/1000)*((mW 12767 : ℝ)*25534*(25534+2)))^2 +
  covarianceVarianceBound 25534 (mW 12767) /
    ((1/1000)*covarianceMeanBound 25534 (mW 12767))^2 +
  normVarianceBound 25534 (mW 12767) / (3*inputVarianceMean 25534 (mW 12767))^2

end BstLean.Part268.WorldRow12767
namespace BstLean.Part268.WorldRow12768
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12768 = 235196069125969 := by
  have hu : mW 12768 ≤ 235196069125969 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12768 ≤ 235196069125968 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12768)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25536 ^ 2)
    ((781250000000000000/125349546878232750214953))
    ((5000000000000000000/802205684094153703440761)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25536) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25536 : ℝ)^2 / (mW 12768 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2025751/1000000000000))/2) * ((1-firstRatio 25536) * √(1-firstRatio 25536) *
      sixthConstant (e1CovarianceRatio 25536 (mW 12768) (1/10^6) rowEps))) /
    (712/10000 - 25536*(1+1/10^6)*((2025751/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25536 (mW 12768) /
    ((1/10^5) * ((mW 12768 : ℝ)*25536*((mW 12768 : ℝ)+25536+1)))^2 +
  8*(mW 12768 : ℝ)*25536*(25536+2)*(25536+3) /
    ((1/1000)*((mW 12768 : ℝ)*25536*(25536+2)))^2 +
  covarianceVarianceBound 25536 (mW 12768) /
    ((1/1000)*covarianceMeanBound 25536 (mW 12768))^2 +
  normVarianceBound 25536 (mW 12768) / (3*inputVarianceMean 25536 (mW 12768))^2

end BstLean.Part268.WorldRow12768
namespace BstLean.Part268.WorldRow12769
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12769 = 235260548044817 := by
  have hu : mW 12769 ≤ 235260548044817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12769 ≤ 235260548044816 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12769)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25538 ^ 2)
    ((25000000000000000000/4011499659368806986202343))
    ((25000000000000000000/4011342579736127496527651)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25538) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25538 : ℝ)^2 / (mW 12769 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202559/100000000000))/2) * ((1-firstRatio 25538) * √(1-firstRatio 25538) *
      sixthConstant (e1CovarianceRatio 25538 (mW 12769) (1/10^6) rowEps))) /
    (712/10000 - 25538*(1+1/10^6)*((202559/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25538 (mW 12769) /
    ((1/10^5) * ((mW 12769 : ℝ)*25538*((mW 12769 : ℝ)+25538+1)))^2 +
  8*(mW 12769 : ℝ)*25538*(25538+2)*(25538+3) /
    ((1/1000)*((mW 12769 : ℝ)*25538*(25538+2)))^2 +
  covarianceVarianceBound 25538 (mW 12769) /
    ((1/1000)*covarianceMeanBound 25538 (mW 12769))^2 +
  normVarianceBound 25538 (mW 12769) / (3*inputVarianceMean 25538 (mW 12769))^2

end BstLean.Part268.WorldRow12769
namespace BstLean.Part268.WorldRow12770
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12770 = 235325039589015 := by
  have hu : mW 12770 ≤ 235325039589015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12770 ≤ 235325039589014 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12770)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25540 ^ 2)
    ((2500000000000000000/401181381863416596552619))
    ((25000000000000000000/4011656739001486475851497)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25540) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25540 : ℝ)^2 / (mW 12770 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202543/100000000000))/2) * ((1-firstRatio 25540) * √(1-firstRatio 25540) *
      sixthConstant (e1CovarianceRatio 25540 (mW 12770) (1/10^6) rowEps))) /
    (712/10000 - 25540*(1+1/10^6)*((202543/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25540 (mW 12770) /
    ((1/10^5) * ((mW 12770 : ℝ)*25540*((mW 12770 : ℝ)+25540+1)))^2 +
  8*(mW 12770 : ℝ)*25540*(25540+2)*(25540+3) /
    ((1/1000)*((mW 12770 : ℝ)*25540*(25540+2)))^2 +
  covarianceVarianceBound 25540 (mW 12770) /
    ((1/1000)*covarianceMeanBound 25540 (mW 12770))^2 +
  normVarianceBound 25540 (mW 12770) / (3*inputVarianceMean 25540 (mW 12770))^2

end BstLean.Part268.WorldRow12770
namespace BstLean.Part268.WorldRow12771
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12771 = 235389543760044 := by
  have hu : mW 12771 ≤ 235389543760044 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12771 ≤ 235389543760043 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12771)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25542 ^ 2)
    ((25000000000000000000/4012127977899524944850037))
    ((25000000000000000000/4011970898266845455175343)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25542) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25542 : ℝ)^2 / (mW 12771 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202527/100000000000))/2) * ((1-firstRatio 25542) * √(1-firstRatio 25542) *
      sixthConstant (e1CovarianceRatio 25542 (mW 12771) (1/10^6) rowEps))) /
    (712/10000 - 25542*(1+1/10^6)*((202527/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25542 (mW 12771) /
    ((1/10^5) * ((mW 12771 : ℝ)*25542*((mW 12771 : ℝ)+25542+1)))^2 +
  8*(mW 12771 : ℝ)*25542*(25542+2)*(25542+3) /
    ((1/1000)*((mW 12771 : ℝ)*25542*(25542+2)))^2 +
  covarianceVarianceBound 25542 (mW 12771) /
    ((1/1000)*covarianceMeanBound 25542 (mW 12771))^2 +
  normVarianceBound 25542 (mW 12771) / (3*inputVarianceMean 25542 (mW 12771))^2

end BstLean.Part268.WorldRow12771
namespace BstLean.Part268.WorldRow12772
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12772 = 235454060559388 := by
  have hu : mW 12772 ≤ 235454060559388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12772 ≤ 235454060559387 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12772)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25544 ^ 2)
    ((6250000000000000000/1003110534291220981043471))
    ((25000000000000000000/4012285057532204434499189)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25544) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25544 : ℝ)^2 / (mW 12772 : ℝ)) * (1 + 1/10^6)^2 *
    √(((202511/100000000000))/2) * ((1-firstRatio 25544) * √(1-firstRatio 25544) *
      sixthConstant (e1CovarianceRatio 25544 (mW 12772) (1/10^6) rowEps))) /
    (712/10000 - 25544*(1+1/10^6)*((202511/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25544 (mW 12772) /
    ((1/10^5) * ((mW 12772 : ℝ)*25544*((mW 12772 : ℝ)+25544+1)))^2 +
  8*(mW 12772 : ℝ)*25544*(25544+2)*(25544+3) /
    ((1/1000)*((mW 12772 : ℝ)*25544*(25544+2)))^2 +
  covarianceVarianceBound 25544 (mW 12772) /
    ((1/1000)*covarianceMeanBound 25544 (mW 12772))^2 +
  normVarianceBound 25544 (mW 12772) / (3*inputVarianceMean 25544 (mW 12772))^2

end BstLean.Part268.WorldRow12772
namespace BstLean.Part268.WorldRow12773
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12773 = 235518589988530 := by
  have hu : mW 12773 ≤ 235518589988530 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12773 ≤ 235518589988529 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12773)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25546 ^ 2)
    ((25000000000000000000/4012756296430242903497731))
    ((5000000000000000000/802519843359512682764607)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25546) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25546 : ℝ)^2 / (mW 12773 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2024949/1000000000000))/2) * ((1-firstRatio 25546) * √(1-firstRatio 25546) *
      sixthConstant (e1CovarianceRatio 25546 (mW 12773) (1/10^6) rowEps))) /
    (712/10000 - 25546*(1+1/10^6)*((2024949/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25546 (mW 12773) /
    ((1/10^5) * ((mW 12773 : ℝ)*25546*((mW 12773 : ℝ)+25546+1)))^2 +
  8*(mW 12773 : ℝ)*25546*(25546+2)*(25546+3) /
    ((1/1000)*((mW 12773 : ℝ)*25546*(25546+2)))^2 +
  covarianceVarianceBound 25546 (mW 12773) /
    ((1/1000)*covarianceMeanBound 25546 (mW 12773))^2 +
  normVarianceBound 25546 (mW 12773) / (3*inputVarianceMean 25546 (mW 12773))^2

end BstLean.Part268.WorldRow12773
namespace BstLean.Part268.WorldRow12774
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12774 = 235583132048954 := by
  have hu : mW 12774 ≤ 235583132048954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12774 ≤ 235583132048953 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12774)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25548 ^ 2)
    ((12500000000000000000/2006535227847800941410789))
    ((25000000000000000000/4012913376062922393146881)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25548) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25548 : ℝ)^2 / (mW 12774 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2024789/1000000000000))/2) * ((1-firstRatio 25548) * √(1-firstRatio 25548) *
      sixthConstant (e1CovarianceRatio 25548 (mW 12774) (1/10^6) rowEps))) /
    (712/10000 - 25548*(1+1/10^6)*((2024789/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25548 (mW 12774) /
    ((1/10^5) * ((mW 12774 : ℝ)*25548*((mW 12774 : ℝ)+25548+1)))^2 +
  8*(mW 12774 : ℝ)*25548*(25548+2)*(25548+3) /
    ((1/1000)*((mW 12774 : ℝ)*25548*(25548+2)))^2 +
  covarianceVarianceBound 25548 (mW 12774) /
    ((1/1000)*covarianceMeanBound 25548 (mW 12774))^2 +
  normVarianceBound 25548 (mW 12774) / (3*inputVarianceMean 25548 (mW 12774))^2

end BstLean.Part268.WorldRow12774
