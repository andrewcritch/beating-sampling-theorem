import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar22
namespace BstLean.Part268.WorldRow12900
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12900 = 243817001558753 := by
  have hu : mW 12900 ≤ 243817001558753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12900 ≤ 243817001558752 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12900)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25800 ^ 2)
    ((250000000000000000/40526545231308332776263))
    ((25000000000000000000/4052497443498153787951477)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25800) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25800 : ℝ)^2 / (mW 12900 : ℝ)) * (1 + 1/10^6)^2 *
    √(((200481/100000000000))/2) * ((1-firstRatio 25800) * √(1-firstRatio 25800) *
      sixthConstant (e1CovarianceRatio 25800 (mW 12900) (1/10^6) rowEps))) /
    (712/10000 - 25800*(1+1/10^6)*((200481/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25800 (mW 12900) /
    ((1/10^5) * ((mW 12900 : ℝ)*25800*((mW 12900 : ℝ)+25800+1)))^2 +
  8*(mW 12900 : ℝ)*25800*(25800+2)*(25800+3) /
    ((1/1000)*((mW 12900 : ℝ)*25800*(25800+2)))^2 +
  covarianceVarianceBound 25800 (mW 12900) /
    ((1/1000)*covarianceMeanBound 25800 (mW 12900))^2 +
  normVarianceBound 25800 (mW 12900) / (3*inputVarianceMean 25800 (mW 12900))^2

end BstLean.Part268.WorldRow12900
namespace BstLean.Part268.WorldRow12901
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12901 = 243883159868717 := by
  have hu : mW 12901 ≤ 243883159868717 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12901 ≤ 243883159868716 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12901)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25802 ^ 2)
    ((25000000000000000000/4052968682396192256950147))
    ((25000000000000000000/4052811602763512767275323)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25802) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25802 : ℝ)^2 / (mW 12901 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2004653/1000000000000))/2) * ((1-firstRatio 25802) * √(1-firstRatio 25802) *
      sixthConstant (e1CovarianceRatio 25802 (mW 12901) (1/10^6) rowEps))) /
    (712/10000 - 25802*(1+1/10^6)*((2004653/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25802 (mW 12901) /
    ((1/10^5) * ((mW 12901 : ℝ)*25802*((mW 12901 : ℝ)+25802+1)))^2 +
  8*(mW 12901 : ℝ)*25802*(25802+2)*(25802+3) /
    ((1/1000)*((mW 12901 : ℝ)*25802*(25802+2)))^2 +
  covarianceVarianceBound 25802 (mW 12901) /
    ((1/1000)*covarianceMeanBound 25802 (mW 12901))^2 +
  normVarianceBound 25802 (mW 12901) / (3*inputVarianceMean 25802 (mW 12901))^2

end BstLean.Part268.WorldRow12901
namespace BstLean.Part268.WorldRow12902
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12902 = 243949331000308 := by
  have hu : mW 12902 ≤ 243949331000308 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12902 ≤ 243949331000307 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12902)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25804 ^ 2)
    ((12500000000000000000/2026641420830775618136997))
    ((25000000000000000000/4053125762028871746599169)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25804) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25804 : ℝ)^2 / (mW 12902 : ℝ)) * (1 + 1/10^6)^2 *
    √(((125281/62500000000))/2) * ((1-firstRatio 25804) * √(1-firstRatio 25804) *
      sixthConstant (e1CovarianceRatio 25804 (mW 12902) (1/10^6) rowEps))) /
    (712/10000 - 25804*(1+1/10^6)*((125281/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25804 (mW 12902) /
    ((1/10^5) * ((mW 12902 : ℝ)*25804*((mW 12902 : ℝ)+25804+1)))^2 +
  8*(mW 12902 : ℝ)*25804*(25804+2)*(25804+3) /
    ((1/1000)*((mW 12902 : ℝ)*25804*(25804+2)))^2 +
  covarianceVarianceBound 25804 (mW 12902) /
    ((1/1000)*covarianceMeanBound 25804 (mW 12902))^2 +
  normVarianceBound 25804 (mW 12902) / (3*inputVarianceMean 25804 (mW 12902))^2

end BstLean.Part268.WorldRow12902
namespace BstLean.Part268.WorldRow12903
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12903 = 244015514955015 := by
  have hu : mW 12903 ≤ 244015514955015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12903 ≤ 244015514955014 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12903)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25806 ^ 2)
    ((25000000000000000000/4053597000926910215597841))
    ((5000000000000000000/810687984258846145184603)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25806) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25806 : ℝ)^2 / (mW 12903 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2004339/1000000000000))/2) * ((1-firstRatio 25806) * √(1-firstRatio 25806) *
      sixthConstant (e1CovarianceRatio 25806 (mW 12903) (1/10^6) rowEps))) /
    (712/10000 - 25806*(1+1/10^6)*((2004339/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25806 (mW 12903) /
    ((1/10^5) * ((mW 12903 : ℝ)*25806*((mW 12903 : ℝ)+25806+1)))^2 +
  8*(mW 12903 : ℝ)*25806*(25806+2)*(25806+3) /
    ((1/1000)*((mW 12903 : ℝ)*25806*(25806+2)))^2 +
  covarianceVarianceBound 25806 (mW 12903) /
    ((1/1000)*covarianceMeanBound 25806 (mW 12903))^2 +
  normVarianceBound 25806 (mW 12903) / (3*inputVarianceMean 25806 (mW 12903))^2

end BstLean.Part268.WorldRow12903
namespace BstLean.Part268.WorldRow12904
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12904 = 244081711734331 := by
  have hu : mW 12904 ≤ 244081711734331 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12904 ≤ 244081711734330 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12904)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25808 ^ 2)
    ((3125000000000000000/506738895024033649365211))
    ((25000000000000000000/4053754080559589705246861)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25808) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25808 : ℝ)^2 / (mW 12904 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1002091/500000000000))/2) * ((1-firstRatio 25808) * √(1-firstRatio 25808) *
      sixthConstant (e1CovarianceRatio 25808 (mW 12904) (1/10^6) rowEps))) /
    (712/10000 - 25808*(1+1/10^6)*((1002091/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25808 (mW 12904) /
    ((1/10^5) * ((mW 12904 : ℝ)*25808*((mW 12904 : ℝ)+25808+1)))^2 +
  8*(mW 12904 : ℝ)*25808*(25808+2)*(25808+3) /
    ((1/1000)*((mW 12904 : ℝ)*25808*(25808+2)))^2 +
  covarianceVarianceBound 25808 (mW 12904) /
    ((1/1000)*covarianceMeanBound 25808 (mW 12904))^2 +
  normVarianceBound 25808 (mW 12904) / (3*inputVarianceMean 25808 (mW 12904))^2

end BstLean.Part268.WorldRow12904
namespace BstLean.Part268.WorldRow12905
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12905 = 244147921339745 := by
  have hu : mW 12905 ≤ 244147921339745 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12905 ≤ 244147921339744 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12905)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25810 ^ 2)
    ((5000000000000000000/810845063891525634849107))
    ((25000000000000000000/4054068239824948684570707)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25810) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25810 : ℝ)^2 / (mW 12905 : ℝ)) * (1 + 1/10^6)^2 *
    √(((80161/40000000000))/2) * ((1-firstRatio 25810) * √(1-firstRatio 25810) *
      sixthConstant (e1CovarianceRatio 25810 (mW 12905) (1/10^6) rowEps))) /
    (712/10000 - 25810*(1+1/10^6)*((80161/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25810 (mW 12905) /
    ((1/10^5) * ((mW 12905 : ℝ)*25810*((mW 12905 : ℝ)+25810+1)))^2 +
  8*(mW 12905 : ℝ)*25810*(25810+2)*(25810+3) /
    ((1/1000)*((mW 12905 : ℝ)*25810*(25810+2)))^2 +
  covarianceVarianceBound 25810 (mW 12905) /
    ((1/1000)*covarianceMeanBound 25810 (mW 12905))^2 +
  normVarianceBound 25810 (mW 12905) / (3*inputVarianceMean 25810 (mW 12905))^2

end BstLean.Part268.WorldRow12905
namespace BstLean.Part268.WorldRow12906
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12906 = 244214143772749 := by
  have hu : mW 12906 ≤ 244214143772749 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12906 ≤ 244214143772748 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12906)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25812 ^ 2)
    ((12500000000000000000/2027269739361493576784691))
    ((25000000000000000000/4054382399090307663894553)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25812) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25812 : ℝ)^2 / (mW 12906 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2003869/1000000000000))/2) * ((1-firstRatio 25812) * √(1-firstRatio 25812) *
      sixthConstant (e1CovarianceRatio 25812 (mW 12906) (1/10^6) rowEps))) /
    (712/10000 - 25812*(1+1/10^6)*((2003869/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25812 (mW 12906) /
    ((1/10^5) * ((mW 12906 : ℝ)*25812*((mW 12906 : ℝ)+25812+1)))^2 +
  8*(mW 12906 : ℝ)*25812*(25812+2)*(25812+3) /
    ((1/1000)*((mW 12906 : ℝ)*25812*(25812+2)))^2 +
  covarianceVarianceBound 25812 (mW 12906) /
    ((1/1000)*covarianceMeanBound 25812 (mW 12906))^2 +
  normVarianceBound 25812 (mW 12906) / (3*inputVarianceMean 25812 (mW 12906))^2

end BstLean.Part268.WorldRow12906
namespace BstLean.Part268.WorldRow12907
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12907 = 244280379034834 := by
  have hu : mW 12907 ≤ 244280379034834 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12907 ≤ 244280379034833 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12907)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25814 ^ 2)
    ((25000000000000000000/4054853637988346132893229))
    ((25000000000000000000/4054696558355666643218399)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25814) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25814 : ℝ)^2 / (mW 12907 : ℝ)) * (1 + 1/10^6)^2 *
    √(((7827/3906250000))/2) * ((1-firstRatio 25814) * √(1-firstRatio 25814) *
      sixthConstant (e1CovarianceRatio 25814 (mW 12907) (1/10^6) rowEps))) /
    (712/10000 - 25814*(1+1/10^6)*((7827/3906250000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25814 (mW 12907) /
    ((1/10^5) * ((mW 12907 : ℝ)*25814*((mW 12907 : ℝ)+25814+1)))^2 +
  8*(mW 12907 : ℝ)*25814*(25814+2)*(25814+3) /
    ((1/1000)*((mW 12907 : ℝ)*25814*(25814+2)))^2 +
  covarianceVarianceBound 25814 (mW 12907) /
    ((1/1000)*covarianceMeanBound 25814 (mW 12907))^2 +
  normVarianceBound 25814 (mW 12907) / (3*inputVarianceMean 25814 (mW 12907))^2

end BstLean.Part268.WorldRow12907
namespace BstLean.Part268.WorldRow12908
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12908 = 244346627127491 := by
  have hu : mW 12908 ≤ 244346627127491 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12908 ≤ 244346627127490 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12908)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25816 ^ 2)
    ((6250000000000000000/1013791949313426278054269))
    ((5000000000000000000/811002143524205124508449)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25816) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25816 : ℝ)^2 / (mW 12908 : ℝ)) * (1 + 1/10^6)^2 *
    √(((400711/200000000000))/2) * ((1-firstRatio 25816) * √(1-firstRatio 25816) *
      sixthConstant (e1CovarianceRatio 25816 (mW 12908) (1/10^6) rowEps))) /
    (712/10000 - 25816*(1+1/10^6)*((400711/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25816 (mW 12908) /
    ((1/10^5) * ((mW 12908 : ℝ)*25816*((mW 12908 : ℝ)+25816+1)))^2 +
  8*(mW 12908 : ℝ)*25816*(25816+2)*(25816+3) /
    ((1/1000)*((mW 12908 : ℝ)*25816*(25816+2)))^2 +
  covarianceVarianceBound 25816 (mW 12908) /
    ((1/1000)*covarianceMeanBound 25816 (mW 12908))^2 +
  normVarianceBound 25816 (mW 12908) / (3*inputVarianceMean 25816 (mW 12908))^2

end BstLean.Part268.WorldRow12908
namespace BstLean.Part268.WorldRow12909
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12909 = 244412888052212 := by
  have hu : mW 12909 ≤ 244412888052212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12909 ≤ 244412888052211 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12909)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25818 ^ 2)
    ((25000000000000000000/4055481956519064091540923))
    ((25000000000000000000/4055324876886384601866091)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25818) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25818 : ℝ)^2 / (mW 12909 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1001699/500000000000))/2) * ((1-firstRatio 25818) * √(1-firstRatio 25818) *
      sixthConstant (e1CovarianceRatio 25818 (mW 12909) (1/10^6) rowEps))) /
    (712/10000 - 25818*(1+1/10^6)*((1001699/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25818 (mW 12909) /
    ((1/10^5) * ((mW 12909 : ℝ)*25818*((mW 12909 : ℝ)+25818+1)))^2 +
  8*(mW 12909 : ℝ)*25818*(25818+2)*(25818+3) /
    ((1/1000)*((mW 12909 : ℝ)*25818*(25818+2)))^2 +
  covarianceVarianceBound 25818 (mW 12909) /
    ((1/1000)*covarianceMeanBound 25818 (mW 12909))^2 +
  normVarianceBound 25818 (mW 12909) / (3*inputVarianceMean 25818 (mW 12909))^2

end BstLean.Part268.WorldRow12909
namespace BstLean.Part268.WorldRow12910
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12910 = 244479161810486 := by
  have hu : mW 12910 ≤ 244479161810486 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12910 ≤ 244479161810485 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12910)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25820 ^ 2)
    ((2500000000000000000/405579611578442307086477))
    ((25000000000000000000/4055639036151743581189937)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25820) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25820 : ℝ)^2 / (mW 12910 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2003241/1000000000000))/2) * ((1-firstRatio 25820) * √(1-firstRatio 25820) *
      sixthConstant (e1CovarianceRatio 25820 (mW 12910) (1/10^6) rowEps))) /
    (712/10000 - 25820*(1+1/10^6)*((2003241/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25820 (mW 12910) /
    ((1/10^5) * ((mW 12910 : ℝ)*25820*((mW 12910 : ℝ)+25820+1)))^2 +
  8*(mW 12910 : ℝ)*25820*(25820+2)*(25820+3) /
    ((1/1000)*((mW 12910 : ℝ)*25820*(25820+2)))^2 +
  covarianceVarianceBound 25820 (mW 12910) /
    ((1/1000)*covarianceMeanBound 25820 (mW 12910))^2 +
  normVarianceBound 25820 (mW 12910) / (3*inputVarianceMean 25820 (mW 12910))^2

end BstLean.Part268.WorldRow12910
namespace BstLean.Part268.WorldRow12911
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12911 = 244545448403807 := by
  have hu : mW 12911 ≤ 244545448403807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12911 ≤ 244545448403806 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12911)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25822 ^ 2)
    ((25000000000000000000/4056110275049782050188617))
    ((25000000000000000000/4055953195417102560513783)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25822) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25822 : ℝ)^2 / (mW 12911 : ℝ)) * (1 + 1/10^6)^2 *
    √(((400617/200000000000))/2) * ((1-firstRatio 25822) * √(1-firstRatio 25822) *
      sixthConstant (e1CovarianceRatio 25822 (mW 12911) (1/10^6) rowEps))) /
    (712/10000 - 25822*(1+1/10^6)*((400617/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25822 (mW 12911) /
    ((1/10^5) * ((mW 12911 : ℝ)*25822*((mW 12911 : ℝ)+25822+1)))^2 +
  8*(mW 12911 : ℝ)*25822*(25822+2)*(25822+3) /
    ((1/1000)*((mW 12911 : ℝ)*25822*(25822+2)))^2 +
  covarianceVarianceBound 25822 (mW 12911) /
    ((1/1000)*covarianceMeanBound 25822 (mW 12911))^2 +
  normVarianceBound 25822 (mW 12911) / (3*inputVarianceMean 25822 (mW 12911))^2

end BstLean.Part268.WorldRow12911
namespace BstLean.Part268.WorldRow12912
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12912 = 244611747833664 := by
  have hu : mW 12912 ≤ 244611747833664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12912 ≤ 244611747833663 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12912)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25824 ^ 2)
    ((1562500000000000000/253526527144696314344529))
    ((25000000000000000000/4056267354682461539837629)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25824) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25824 : ℝ)^2 / (mW 12912 : ℝ)) * (1 + 1/10^6)^2 *
    √(((125183/62500000000))/2) * ((1-firstRatio 25824) * √(1-firstRatio 25824) *
      sixthConstant (e1CovarianceRatio 25824 (mW 12912) (1/10^6) rowEps))) /
    (712/10000 - 25824*(1+1/10^6)*((125183/62500000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25824 (mW 12912) /
    ((1/10^5) * ((mW 12912 : ℝ)*25824*((mW 12912 : ℝ)+25824+1)))^2 +
  8*(mW 12912 : ℝ)*25824*(25824+2)*(25824+3) /
    ((1/1000)*((mW 12912 : ℝ)*25824*(25824+2)))^2 +
  covarianceVarianceBound 25824 (mW 12912) /
    ((1/1000)*covarianceMeanBound 25824 (mW 12912))^2 +
  normVarianceBound 25824 (mW 12912) / (3*inputVarianceMean 25824 (mW 12912))^2

end BstLean.Part268.WorldRow12912
namespace BstLean.Part268.WorldRow12913
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12913 = 244678060101550 := by
  have hu : mW 12913 ≤ 244678060101550 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12913 ≤ 244678060101549 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12913)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25826 ^ 2)
    ((25000000000000000000/4056738593580500008836311))
    ((1000000000000000000/162263260557912820766459)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25826) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25826 : ℝ)^2 / (mW 12913 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2002771/1000000000000))/2) * ((1-firstRatio 25826) * √(1-firstRatio 25826) *
      sixthConstant (e1CovarianceRatio 25826 (mW 12913) (1/10^6) rowEps))) /
    (712/10000 - 25826*(1+1/10^6)*((2002771/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25826 (mW 12913) /
    ((1/10^5) * ((mW 12913 : ℝ)*25826*((mW 12913 : ℝ)+25826+1)))^2 +
  8*(mW 12913 : ℝ)*25826*(25826+2)*(25826+3) /
    ((1/1000)*((mW 12913 : ℝ)*25826*(25826+2)))^2 +
  covarianceVarianceBound 25826 (mW 12913) /
    ((1/1000)*covarianceMeanBound 25826 (mW 12913))^2 +
  normVarianceBound 25826 (mW 12913) / (3*inputVarianceMean 25826 (mW 12913))^2

end BstLean.Part268.WorldRow12913
namespace BstLean.Part268.WorldRow12914
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12914 = 244744385208955 := by
  have hu : mW 12914 ≤ 244744385208955 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12914 ≤ 244744385208954 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12914)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25828 ^ 2)
    ((12500000000000000000/2028526376422929494080079))
    ((25000000000000000000/4056895673213179498485321)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25828) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25828 : ℝ)^2 / (mW 12914 : ℝ)) * (1 + 1/10^6)^2 *
    √(((400523/200000000000))/2) * ((1-firstRatio 25828) * √(1-firstRatio 25828) *
      sixthConstant (e1CovarianceRatio 25828 (mW 12914) (1/10^6) rowEps))) /
    (712/10000 - 25828*(1+1/10^6)*((400523/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25828 (mW 12914) /
    ((1/10^5) * ((mW 12914 : ℝ)*25828*((mW 12914 : ℝ)+25828+1)))^2 +
  8*(mW 12914 : ℝ)*25828*(25828+2)*(25828+3) /
    ((1/1000)*((mW 12914 : ℝ)*25828*(25828+2)))^2 +
  covarianceVarianceBound 25828 (mW 12914) /
    ((1/1000)*covarianceMeanBound 25828 (mW 12914))^2 +
  normVarianceBound 25828 (mW 12914) / (3*inputVarianceMean 25828 (mW 12914))^2

end BstLean.Part268.WorldRow12914
namespace BstLean.Part268.WorldRow12915
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12915 = 244810723157371 := by
  have hu : mW 12915 ≤ 244810723157371 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12915 ≤ 244810723157370 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12915)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25830 ^ 2)
    ((5000000000000000000/811473382422243593496801))
    ((25000000000000000000/4057209832478538477809167)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25830) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25830 : ℝ)^2 / (mW 12915 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1001229/500000000000))/2) * ((1-firstRatio 25830) * √(1-firstRatio 25830) *
      sixthConstant (e1CovarianceRatio 25830 (mW 12915) (1/10^6) rowEps))) /
    (712/10000 - 25830*(1+1/10^6)*((1001229/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25830 (mW 12915) /
    ((1/10^5) * ((mW 12915 : ℝ)*25830*((mW 12915 : ℝ)+25830+1)))^2 +
  8*(mW 12915 : ℝ)*25830*(25830+2)*(25830+3) /
    ((1/1000)*((mW 12915 : ℝ)*25830*(25830+2)))^2 +
  covarianceVarianceBound 25830 (mW 12915) /
    ((1/1000)*covarianceMeanBound 25830 (mW 12915))^2 +
  normVarianceBound 25830 (mW 12915) / (3*inputVarianceMean 25830 (mW 12915))^2

end BstLean.Part268.WorldRow12915
namespace BstLean.Part268.WorldRow12916
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12916 = 244877073948291 := by
  have hu : mW 12916 ≤ 244877073948291 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12916 ≤ 244877073948290 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12916)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25832 ^ 2)
    ((6250000000000000000/1014420267844144236701963))
    ((25000000000000000000/4057523991743897457133013)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25832) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25832 : ℝ)^2 / (mW 12916 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2002301/1000000000000))/2) * ((1-firstRatio 25832) * √(1-firstRatio 25832) *
      sixthConstant (e1CovarianceRatio 25832 (mW 12916) (1/10^6) rowEps))) /
    (712/10000 - 25832*(1+1/10^6)*((2002301/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25832 (mW 12916) /
    ((1/10^5) * ((mW 12916 : ℝ)*25832*((mW 12916 : ℝ)+25832+1)))^2 +
  8*(mW 12916 : ℝ)*25832*(25832+2)*(25832+3) /
    ((1/1000)*((mW 12916 : ℝ)*25832*(25832+2)))^2 +
  covarianceVarianceBound 25832 (mW 12916) /
    ((1/1000)*covarianceMeanBound 25832 (mW 12916))^2 +
  normVarianceBound 25832 (mW 12916) / (3*inputVarianceMean 25832 (mW 12916))^2

end BstLean.Part268.WorldRow12916
namespace BstLean.Part268.WorldRow12917
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12917 = 244943437583204 := by
  have hu : mW 12917 ≤ 244943437583204 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12917 ≤ 244943437583203 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12917)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25834 ^ 2)
    ((25000000000000000000/4057995230641935926131699))
    ((25000000000000000000/4057838151009256436456859)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25834) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25834 : ℝ)^2 / (mW 12917 : ℝ)) * (1 + 1/10^6)^2 *
    √(((400429/200000000000))/2) * ((1-firstRatio 25834) * √(1-firstRatio 25834) *
      sixthConstant (e1CovarianceRatio 25834 (mW 12917) (1/10^6) rowEps))) /
    (712/10000 - 25834*(1+1/10^6)*((400429/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25834 (mW 12917) /
    ((1/10^5) * ((mW 12917 : ℝ)*25834*((mW 12917 : ℝ)+25834+1)))^2 +
  8*(mW 12917 : ℝ)*25834*(25834+2)*(25834+3) /
    ((1/1000)*((mW 12917 : ℝ)*25834*(25834+2)))^2 +
  covarianceVarianceBound 25834 (mW 12917) /
    ((1/1000)*covarianceMeanBound 25834 (mW 12917))^2 +
  normVarianceBound 25834 (mW 12917) / (3*inputVarianceMean 25834 (mW 12917))^2

end BstLean.Part268.WorldRow12917
namespace BstLean.Part268.WorldRow12918
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12918 = 245009814063604 := by
  have hu : mW 12918 ≤ 245009814063604 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12918 ≤ 245009814063603 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12918)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25836 ^ 2)
    ((12500000000000000000/2029154694953647452727773))
    ((5000000000000000000/811630462054923083156141)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25836) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25836 : ℝ)^2 / (mW 12918 : ℝ)) * (1 + 1/10^6)^2 *
    √(((500497/250000000000))/2) * ((1-firstRatio 25836) * √(1-firstRatio 25836) *
      sixthConstant (e1CovarianceRatio 25836 (mW 12918) (1/10^6) rowEps))) /
    (712/10000 - 25836*(1+1/10^6)*((500497/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25836 (mW 12918) /
    ((1/10^5) * ((mW 12918 : ℝ)*25836*((mW 12918 : ℝ)+25836+1)))^2 +
  8*(mW 12918 : ℝ)*25836*(25836+2)*(25836+3) /
    ((1/1000)*((mW 12918 : ℝ)*25836*(25836+2)))^2 +
  covarianceVarianceBound 25836 (mW 12918) /
    ((1/1000)*covarianceMeanBound 25836 (mW 12918))^2 +
  normVarianceBound 25836 (mW 12918) / (3*inputVarianceMean 25836 (mW 12918))^2

end BstLean.Part268.WorldRow12918
namespace BstLean.Part268.WorldRow12919
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12919 = 245076203390982 := by
  have hu : mW 12919 ≤ 245076203390982 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12919 ≤ 245076203390981 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12919)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25838 ^ 2)
    ((25000000000000000000/4058623549172653884779393))
    ((25000000000000000000/4058466469539974395104551)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25838) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25838 : ℝ)^2 / (mW 12919 : ℝ)) * (1 + 1/10^6)^2 *
    √(((250229/125000000000))/2) * ((1-firstRatio 25838) * √(1-firstRatio 25838) *
      sixthConstant (e1CovarianceRatio 25838 (mW 12919) (1/10^6) rowEps))) /
    (712/10000 - 25838*(1+1/10^6)*((250229/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25838 (mW 12919) /
    ((1/10^5) * ((mW 12919 : ℝ)*25838*((mW 12919 : ℝ)+25838+1)))^2 +
  8*(mW 12919 : ℝ)*25838*(25838+2)*(25838+3) /
    ((1/1000)*((mW 12919 : ℝ)*25838*(25838+2)))^2 +
  covarianceVarianceBound 25838 (mW 12919) /
    ((1/1000)*covarianceMeanBound 25838 (mW 12919))^2 +
  normVarianceBound 25838 (mW 12919) / (3*inputVarianceMean 25838 (mW 12919))^2

end BstLean.Part268.WorldRow12919
namespace BstLean.Part268.WorldRow12920
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12920 = 245142605566829 := by
  have hu : mW 12920 ≤ 245142605566829 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12920 ≤ 245142605566828 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12920)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25840 ^ 2)
    ((625000000000000000/101473442710950321602581))
    ((25000000000000000000/4058780628805333374428397)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25840) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25840 : ℝ)^2 / (mW 12920 : ℝ)) * (1 + 1/10^6)^2 *
    √(((80067/40000000000))/2) * ((1-firstRatio 25840) * √(1-firstRatio 25840) *
      sixthConstant (e1CovarianceRatio 25840 (mW 12920) (1/10^6) rowEps))) /
    (712/10000 - 25840*(1+1/10^6)*((80067/40000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25840 (mW 12920) /
    ((1/10^5) * ((mW 12920 : ℝ)*25840*((mW 12920 : ℝ)+25840+1)))^2 +
  8*(mW 12920 : ℝ)*25840*(25840+2)*(25840+3) /
    ((1/1000)*((mW 12920 : ℝ)*25840*(25840+2)))^2 +
  covarianceVarianceBound 25840 (mW 12920) /
    ((1/1000)*covarianceMeanBound 25840 (mW 12920))^2 +
  normVarianceBound 25840 (mW 12920) / (3*inputVarianceMean 25840 (mW 12920))^2

end BstLean.Part268.WorldRow12920
namespace BstLean.Part268.WorldRow12921
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12921 = 245209020592638 := by
  have hu : mW 12921 ≤ 245209020592638 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12921 ≤ 245209020592637 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12921)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25842 ^ 2)
    ((25000000000000000000/4059251867703371843427087))
    ((25000000000000000000/4059094788070692353752243)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25842) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25842 : ℝ)^2 / (mW 12921 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2001519/1000000000000))/2) * ((1-firstRatio 25842) * √(1-firstRatio 25842) *
      sixthConstant (e1CovarianceRatio 25842 (mW 12921) (1/10^6) rowEps))) /
    (712/10000 - 25842*(1+1/10^6)*((2001519/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25842 (mW 12921) /
    ((1/10^5) * ((mW 12921 : ℝ)*25842*((mW 12921 : ℝ)+25842+1)))^2 +
  8*(mW 12921 : ℝ)*25842*(25842+2)*(25842+3) /
    ((1/1000)*((mW 12921 : ℝ)*25842*(25842+2)))^2 +
  covarianceVarianceBound 25842 (mW 12921) /
    ((1/1000)*covarianceMeanBound 25842 (mW 12921))^2 +
  normVarianceBound 25842 (mW 12921) / (3*inputVarianceMean 25842 (mW 12921))^2

end BstLean.Part268.WorldRow12921
namespace BstLean.Part268.WorldRow12922
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12922 = 245275448469900 := by
  have hu : mW 12922 ≤ 245275448469900 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12922 ≤ 245275448469899 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12922)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25844 ^ 2)
    ((12500000000000000000/2029783013484365411375467))
    ((25000000000000000000/4059408947336051333076089)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25844) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25844 : ℝ)^2 / (mW 12922 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1000681/500000000000))/2) * ((1-firstRatio 25844) * √(1-firstRatio 25844) *
      sixthConstant (e1CovarianceRatio 25844 (mW 12922) (1/10^6) rowEps))) /
    (712/10000 - 25844*(1+1/10^6)*((1000681/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25844 (mW 12922) /
    ((1/10^5) * ((mW 12922 : ℝ)*25844*((mW 12922 : ℝ)+25844+1)))^2 +
  8*(mW 12922 : ℝ)*25844*(25844+2)*(25844+3) /
    ((1/1000)*((mW 12922 : ℝ)*25844*(25844+2)))^2 +
  covarianceVarianceBound 25844 (mW 12922) /
    ((1/1000)*covarianceMeanBound 25844 (mW 12922))^2 +
  normVarianceBound 25844 (mW 12922) / (3*inputVarianceMean 25844 (mW 12922))^2

end BstLean.Part268.WorldRow12922
namespace BstLean.Part268.WorldRow12923
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12923 = 245341889200107 := by
  have hu : mW 12923 ≤ 245341889200107 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12923 ≤ 245341889200106 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12923)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25846 ^ 2)
    ((25000000000000000000/4059880186234089802074781))
    ((5000000000000000000/811944621320282062479987)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25846) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25846 : ℝ)^2 / (mW 12923 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1000603/500000000000))/2) * ((1-firstRatio 25846) * √(1-firstRatio 25846) *
      sixthConstant (e1CovarianceRatio 25846 (mW 12923) (1/10^6) rowEps))) /
    (712/10000 - 25846*(1+1/10^6)*((1000603/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25846 (mW 12923) /
    ((1/10^5) * ((mW 12923 : ℝ)*25846*((mW 12923 : ℝ)+25846+1)))^2 +
  8*(mW 12923 : ℝ)*25846*(25846+2)*(25846+3) /
    ((1/1000)*((mW 12923 : ℝ)*25846*(25846+2)))^2 +
  covarianceVarianceBound 25846 (mW 12923) /
    ((1/1000)*covarianceMeanBound 25846 (mW 12923))^2 +
  normVarianceBound 25846 (mW 12923) / (3*inputVarianceMean 25846 (mW 12923))^2

end BstLean.Part268.WorldRow12923
namespace BstLean.Part268.WorldRow12924
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12924 = 245408342784751 := by
  have hu : mW 12924 ≤ 245408342784751 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12924 ≤ 245408342784750 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12924)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25848 ^ 2)
    ((6250000000000000000/1015048586374862195349657))
    ((25000000000000000000/4060037265866769291723781)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25848) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25848 : ℝ)^2 / (mW 12924 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2001049/1000000000000))/2) * ((1-firstRatio 25848) * √(1-firstRatio 25848) *
      sixthConstant (e1CovarianceRatio 25848 (mW 12924) (1/10^6) rowEps))) /
    (712/10000 - 25848*(1+1/10^6)*((2001049/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25848 (mW 12924) /
    ((1/10^5) * ((mW 12924 : ℝ)*25848*((mW 12924 : ℝ)+25848+1)))^2 +
  8*(mW 12924 : ℝ)*25848*(25848+2)*(25848+3) /
    ((1/1000)*((mW 12924 : ℝ)*25848*(25848+2)))^2 +
  covarianceVarianceBound 25848 (mW 12924) /
    ((1/1000)*covarianceMeanBound 25848 (mW 12924))^2 +
  normVarianceBound 25848 (mW 12924) / (3*inputVarianceMean 25848 (mW 12924))^2

end BstLean.Part268.WorldRow12924
