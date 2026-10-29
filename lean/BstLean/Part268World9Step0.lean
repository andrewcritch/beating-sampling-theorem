import BstLean.Part250Kernel
import BstLean.Part227Guards
import BstLean.Part243Row
import BstLean.Part197Log
import BstLean.Part268Scalar9
namespace BstLean.Part268.WorldRow12575
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12575 = 222986195612090 := by
  have hu : mW 12575 ≤ 222986195612090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12575 ≤ 222986195612089 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12575)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25150 ^ 2)
    ((1000000000000000000/158022110475566599895041))
    ((25000000000000000000/3950395682256485507701527)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25150) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25150 : ℝ)^2 / (mW 12575 : ℝ)) * (1 + 1/10^6)^2 *
    √(((205717/100000000000))/2) * ((1-firstRatio 25150) * √(1-firstRatio 25150) *
      sixthConstant (e1CovarianceRatio 25150 (mW 12575) (1/10^6) rowEps))) /
    (712/10000 - 25150*(1+1/10^6)*((205717/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25150 (mW 12575) /
    ((1/10^5) * ((mW 12575 : ℝ)*25150*((mW 12575 : ℝ)+25150+1)))^2 +
  8*(mW 12575 : ℝ)*25150*(25150+2)*(25150+3) /
    ((1/1000)*((mW 12575 : ℝ)*25150*(25150+2)))^2 +
  covarianceVarianceBound 25150 (mW 12575) /
    ((1/1000)*covarianceMeanBound 25150 (mW 12575))^2 +
  normVarianceBound 25150 (mW 12575) / (3*inputVarianceMean 25150 (mW 12575))^2

end BstLean.Part268.WorldRow12575
namespace BstLean.Part268.WorldRow12576
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12576 = 223048265533952 := by
  have hu : mW 12576 ≤ 223048265533952 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12576 ≤ 223048265533951 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12576)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25152 ^ 2)
    ((781250000000000000/123464591286078874271871))
    ((25000000000000000000/3950709841521844487025373)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25152) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25152 : ℝ)^2 / (mW 12576 : ℝ)) * (1 + 1/10^6)^2 *
    √(((411401/200000000000))/2) * ((1-firstRatio 25152) * √(1-firstRatio 25152) *
      sixthConstant (e1CovarianceRatio 25152 (mW 12576) (1/10^6) rowEps))) /
    (712/10000 - 25152*(1+1/10^6)*((411401/200000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25152 (mW 12576) /
    ((1/10^5) * ((mW 12576 : ℝ)*25152*((mW 12576 : ℝ)+25152+1)))^2 +
  8*(mW 12576 : ℝ)*25152*(25152+2)*(25152+3) /
    ((1/1000)*((mW 12576 : ℝ)*25152*(25152+2)))^2 +
  covarianceVarianceBound 25152 (mW 12576) /
    ((1/1000)*covarianceMeanBound 25152 (mW 12576))^2 +
  normVarianceBound 25152 (mW 12576) / (3*inputVarianceMean 25152 (mW 12576))^2

end BstLean.Part268.WorldRow12576
namespace BstLean.Part268.WorldRow12577
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12577 = 223110347796004 := by
  have hu : mW 12577 ≤ 223110347796004 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12577 ≤ 223110347796003 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12577)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25154 ^ 2)
    ((25000000000000000000/3951181080419882956023719))
    ((25000000000000000000/3951024000787203466349219)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25154) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25154 : ℝ)^2 / (mW 12577 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2056839/1000000000000))/2) * ((1-firstRatio 25154) * √(1-firstRatio 25154) *
      sixthConstant (e1CovarianceRatio 25154 (mW 12577) (1/10^6) rowEps))) /
    (712/10000 - 25154*(1+1/10^6)*((2056839/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25154 (mW 12577) /
    ((1/10^5) * ((mW 12577 : ℝ)*25154*((mW 12577 : ℝ)+25154+1)))^2 +
  8*(mW 12577 : ℝ)*25154*(25154+2)*(25154+3) /
    ((1/1000)*((mW 12577 : ℝ)*25154*(25154+2)))^2 +
  covarianceVarianceBound 25154 (mW 12577) /
    ((1/1000)*covarianceMeanBound 25154 (mW 12577))^2 +
  normVarianceBound 25154 (mW 12577) / (3*inputVarianceMean 25154 (mW 12577))^2

end BstLean.Part268.WorldRow12577
namespace BstLean.Part268.WorldRow12578
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12578 = 223172442399718 := by
  have hu : mW 12578 ≤ 223172442399718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12578 ≤ 223172442399717 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12578)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25156 ^ 2)
    ((12500000000000000000/1975747619842620967673783))
    ((5000000000000000000/790267632010512489134613)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25156) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25156 : ℝ)^2 / (mW 12578 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1028337/500000000000))/2) * ((1-firstRatio 25156) * √(1-firstRatio 25156) *
      sixthConstant (e1CovarianceRatio 25156 (mW 12578) (1/10^6) rowEps))) /
    (712/10000 - 25156*(1+1/10^6)*((1028337/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25156 (mW 12578) /
    ((1/10^5) * ((mW 12578 : ℝ)*25156*((mW 12578 : ℝ)+25156+1)))^2 +
  8*(mW 12578 : ℝ)*25156*(25156+2)*(25156+3) /
    ((1/1000)*((mW 12578 : ℝ)*25156*(25156+2)))^2 +
  covarianceVarianceBound 25156 (mW 12578) /
    ((1/1000)*covarianceMeanBound 25156 (mW 12578))^2 +
  normVarianceBound 25156 (mW 12578) / (3*inputVarianceMean 25156 (mW 12578))^2

end BstLean.Part268.WorldRow12578
namespace BstLean.Part268.WorldRow12579
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12579 = 223234549346566 := by
  have hu : mW 12579 ≤ 223234549346566 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12579 ≤ 223234549346565 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12579)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25158 ^ 2)
    ((25000000000000000000/3951809398950600914671413))
    ((25000000000000000000/3951652319317921424996911)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25158) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25158 : ℝ)^2 / (mW 12579 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2056509/1000000000000))/2) * ((1-firstRatio 25158) * √(1-firstRatio 25158) *
      sixthConstant (e1CovarianceRatio 25158 (mW 12579) (1/10^6) rowEps))) /
    (712/10000 - 25158*(1+1/10^6)*((2056509/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25158 (mW 12579) /
    ((1/10^5) * ((mW 12579 : ℝ)*25158*((mW 12579 : ℝ)+25158+1)))^2 +
  8*(mW 12579 : ℝ)*25158*(25158+2)*(25158+3) /
    ((1/1000)*((mW 12579 : ℝ)*25158*(25158+2)))^2 +
  covarianceVarianceBound 25158 (mW 12579) /
    ((1/1000)*covarianceMeanBound 25158 (mW 12579))^2 +
  normVarianceBound 25158 (mW 12579) / (3*inputVarianceMean 25158 (mW 12579))^2

end BstLean.Part268.WorldRow12579
namespace BstLean.Part268.WorldRow12580
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12580 = 223296668638020 := by
  have hu : mW 12580 ≤ 223296668638020 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12580 ≤ 223296668638019 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12580)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25160 ^ 2)
    ((1250000000000000000/197606177910797994699763))
    ((25000000000000000000/3951966478583280404320757)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25160) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25160 : ℝ)^2 / (mW 12580 : ℝ)) * (1 + 1/10^6)^2 *
    √(((257043/125000000000))/2) * ((1-firstRatio 25160) * √(1-firstRatio 25160) *
      sixthConstant (e1CovarianceRatio 25160 (mW 12580) (1/10^6) rowEps))) /
    (712/10000 - 25160*(1+1/10^6)*((257043/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25160 (mW 12580) /
    ((1/10^5) * ((mW 12580 : ℝ)*25160*((mW 12580 : ℝ)+25160+1)))^2 +
  8*(mW 12580 : ℝ)*25160*(25160+2)*(25160+3) /
    ((1/1000)*((mW 12580 : ℝ)*25160*(25160+2)))^2 +
  covarianceVarianceBound 25160 (mW 12580) /
    ((1/1000)*covarianceMeanBound 25160 (mW 12580))^2 +
  normVarianceBound 25160 (mW 12580) / (3*inputVarianceMean 25160 (mW 12580))^2

end BstLean.Part268.WorldRow12580
namespace BstLean.Part268.WorldRow12581
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12581 = 223358800275552 := by
  have hu : mW 12581 ≤ 223358800275552 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12581 ≤ 223358800275551 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12581)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25162 ^ 2)
    ((25000000000000000000/3952437717481318873319107))
    ((25000000000000000000/3952280637848639383644603)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25162) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25162 : ℝ)^2 / (mW 12581 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2056179/1000000000000))/2) * ((1-firstRatio 25162) * √(1-firstRatio 25162) *
      sixthConstant (e1CovarianceRatio 25162 (mW 12581) (1/10^6) rowEps))) /
    (712/10000 - 25162*(1+1/10^6)*((2056179/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25162 (mW 12581) /
    ((1/10^5) * ((mW 12581 : ℝ)*25162*((mW 12581 : ℝ)+25162+1)))^2 +
  8*(mW 12581 : ℝ)*25162*(25162+2)*(25162+3) /
    ((1/1000)*((mW 12581 : ℝ)*25162*(25162+2)))^2 +
  covarianceVarianceBound 25162 (mW 12581) /
    ((1/1000)*covarianceMeanBound 25162 (mW 12581))^2 +
  normVarianceBound 25162 (mW 12581) / (3*inputVarianceMean 25162 (mW 12581))^2

end BstLean.Part268.WorldRow12581
namespace BstLean.Part268.WorldRow12582
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12582 = 223420944260634 := by
  have hu : mW 12582 ≤ 223420944260634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12582 ≤ 223420944260633 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12582)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25164 ^ 2)
    ((12500000000000000000/1976375938373338926321477))
    ((25000000000000000000/3952594797113998362968449)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25164) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25164 : ℝ)^2 / (mW 12582 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2056013/1000000000000))/2) * ((1-firstRatio 25164) * √(1-firstRatio 25164) *
      sixthConstant (e1CovarianceRatio 25164 (mW 12582) (1/10^6) rowEps))) /
    (712/10000 - 25164*(1+1/10^6)*((2056013/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25164 (mW 12582) /
    ((1/10^5) * ((mW 12582 : ℝ)*25164*((mW 12582 : ℝ)+25164+1)))^2 +
  8*(mW 12582 : ℝ)*25164*(25164+2)*(25164+3) /
    ((1/1000)*((mW 12582 : ℝ)*25164*(25164+2)))^2 +
  covarianceVarianceBound 25164 (mW 12582) /
    ((1/1000)*covarianceMeanBound 25164 (mW 12582))^2 +
  normVarianceBound 25164 (mW 12582) / (3*inputVarianceMean 25164 (mW 12582))^2

end BstLean.Part268.WorldRow12582
namespace BstLean.Part268.WorldRow12583
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12583 = 223483100594738 := by
  have hu : mW 12583 ≤ 223483100594738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12583 ≤ 223483100594737 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12583)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25166 ^ 2)
    ((25000000000000000000/3953066036012036831966801))
    ((5000000000000000000/790581791275871468458459)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25166) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25166 : ℝ)^2 / (mW 12583 : ℝ)) * (1 + 1/10^6)^2 *
    √(((256981/125000000000))/2) * ((1-firstRatio 25166) * √(1-firstRatio 25166) *
      sixthConstant (e1CovarianceRatio 25166 (mW 12583) (1/10^6) rowEps))) /
    (712/10000 - 25166*(1+1/10^6)*((256981/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25166 (mW 12583) /
    ((1/10^5) * ((mW 12583 : ℝ)*25166*((mW 12583 : ℝ)+25166+1)))^2 +
  8*(mW 12583 : ℝ)*25166*(25166+2)*(25166+3) /
    ((1/1000)*((mW 12583 : ℝ)*25166*(25166+2)))^2 +
  covarianceVarianceBound 25166 (mW 12583) /
    ((1/1000)*covarianceMeanBound 25166 (mW 12583))^2 +
  normVarianceBound 25166 (mW 12583) / (3*inputVarianceMean 25166 (mW 12583))^2

end BstLean.Part268.WorldRow12583
namespace BstLean.Part268.WorldRow12584
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12584 = 223545269279337 := by
  have hu : mW 12584 ≤ 223545269279337 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12584 ≤ 223545269279336 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12584)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25168 ^ 2)
    ((3125000000000000000/494172524409674476411331))
    ((25000000000000000000/3953223115644716321616141)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25168) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25168 : ℝ)^2 / (mW 12584 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2055683/1000000000000))/2) * ((1-firstRatio 25168) * √(1-firstRatio 25168) *
      sixthConstant (e1CovarianceRatio 25168 (mW 12584) (1/10^6) rowEps))) /
    (712/10000 - 25168*(1+1/10^6)*((2055683/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25168 (mW 12584) /
    ((1/10^5) * ((mW 12584 : ℝ)*25168*((mW 12584 : ℝ)+25168+1)))^2 +
  8*(mW 12584 : ℝ)*25168*(25168+2)*(25168+3) /
    ((1/1000)*((mW 12584 : ℝ)*25168*(25168+2)))^2 +
  covarianceVarianceBound 25168 (mW 12584) /
    ((1/1000)*covarianceMeanBound 25168 (mW 12584))^2 +
  normVarianceBound 25168 (mW 12584) / (3*inputVarianceMean 25168 (mW 12584))^2

end BstLean.Part268.WorldRow12584
namespace BstLean.Part268.WorldRow12585
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12585 = 223607450315902 := by
  have hu : mW 12585 ≤ 223607450315902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12585 ≤ 223607450315901 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12585)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25170 ^ 2)
    ((5000000000000000000/790738870908550958122899))
    ((25000000000000000000/3953537274910075300939987)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25170) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25170 : ℝ)^2 / (mW 12585 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1027759/500000000000))/2) * ((1-firstRatio 25170) * √(1-firstRatio 25170) *
      sixthConstant (e1CovarianceRatio 25170 (mW 12585) (1/10^6) rowEps))) /
    (712/10000 - 25170*(1+1/10^6)*((1027759/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25170 (mW 12585) /
    ((1/10^5) * ((mW 12585 : ℝ)*25170*((mW 12585 : ℝ)+25170+1)))^2 +
  8*(mW 12585 : ℝ)*25170*(25170+2)*(25170+3) /
    ((1/1000)*((mW 12585 : ℝ)*25170*(25170+2)))^2 +
  covarianceVarianceBound 25170 (mW 12585) /
    ((1/1000)*covarianceMeanBound 25170 (mW 12585))^2 +
  normVarianceBound 25170 (mW 12585) / (3*inputVarianceMean 25170 (mW 12585))^2

end BstLean.Part268.WorldRow12585
namespace BstLean.Part268.WorldRow12586
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12586 = 223669643705907 := by
  have hu : mW 12586 ≤ 223669643705907 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12586 ≤ 223669643705906 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12586)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25172 ^ 2)
    ((12500000000000000000/1977004256904056884969171))
    ((25000000000000000000/3953851434175434280263833)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25172) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25172 : ℝ)^2 / (mW 12586 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2055353/1000000000000))/2) * ((1-firstRatio 25172) * √(1-firstRatio 25172) *
      sixthConstant (e1CovarianceRatio 25172 (mW 12586) (1/10^6) rowEps))) /
    (712/10000 - 25172*(1+1/10^6)*((2055353/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25172 (mW 12586) /
    ((1/10^5) * ((mW 12586 : ℝ)*25172*((mW 12586 : ℝ)+25172+1)))^2 +
  8*(mW 12586 : ℝ)*25172*(25172+2)*(25172+3) /
    ((1/1000)*((mW 12586 : ℝ)*25172*(25172+2)))^2 +
  covarianceVarianceBound 25172 (mW 12586) /
    ((1/1000)*covarianceMeanBound 25172 (mW 12586))^2 +
  normVarianceBound 25172 (mW 12586) / (3*inputVarianceMean 25172 (mW 12586))^2

end BstLean.Part268.WorldRow12586
namespace BstLean.Part268.WorldRow12587
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12587 = 223731849450823 := by
  have hu : mW 12587 ≤ 223731849450823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12587 ≤ 223731849450822 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12587)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25174 ^ 2)
    ((25000000000000000000/3954322673073472749262189))
    ((25000000000000000000/3954165593440793259587679)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25174) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25174 : ℝ)^2 / (mW 12587 : ℝ)) * (1 + 1/10^6)^2 *
    √(((513797/250000000000))/2) * ((1-firstRatio 25174) * √(1-firstRatio 25174) *
      sixthConstant (e1CovarianceRatio 25174 (mW 12587) (1/10^6) rowEps))) /
    (712/10000 - 25174*(1+1/10^6)*((513797/250000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25174 (mW 12587) /
    ((1/10^5) * ((mW 12587 : ℝ)*25174*((mW 12587 : ℝ)+25174+1)))^2 +
  8*(mW 12587 : ℝ)*25174*(25174+2)*(25174+3) /
    ((1/1000)*((mW 12587 : ℝ)*25174*(25174+2)))^2 +
  covarianceVarianceBound 25174 (mW 12587) /
    ((1/1000)*covarianceMeanBound 25174 (mW 12587))^2 +
  normVarianceBound 25174 (mW 12587) / (3*inputVarianceMean 25174 (mW 12587))^2

end BstLean.Part268.WorldRow12587
namespace BstLean.Part268.WorldRow12588
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12588 = 223794067552124 := by
  have hu : mW 12588 ≤ 223794067552124 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12588 ≤ 223794067552123 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12588)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25176 ^ 2)
    ((6250000000000000000/988659208084707932146509))
    ((1000000000000000000/158179190108246089556461)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25176) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25176 : ℝ)^2 / (mW 12588 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2055023/1000000000000))/2) * ((1-firstRatio 25176) * √(1-firstRatio 25176) *
      sixthConstant (e1CovarianceRatio 25176 (mW 12588) (1/10^6) rowEps))) /
    (712/10000 - 25176*(1+1/10^6)*((2055023/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25176 (mW 12588) /
    ((1/10^5) * ((mW 12588 : ℝ)*25176*((mW 12588 : ℝ)+25176+1)))^2 +
  8*(mW 12588 : ℝ)*25176*(25176+2)*(25176+3) /
    ((1/1000)*((mW 12588 : ℝ)*25176*(25176+2)))^2 +
  covarianceVarianceBound 25176 (mW 12588) /
    ((1/1000)*covarianceMeanBound 25176 (mW 12588))^2 +
  normVarianceBound 25176 (mW 12588) / (3*inputVarianceMean 25176 (mW 12588))^2

end BstLean.Part268.WorldRow12588
namespace BstLean.Part268.WorldRow12589
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12589 = 223856298011281 := by
  have hu : mW 12589 ≤ 223856298011281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12589 ≤ 223856298011280 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12589)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25178 ^ 2)
    ((25000000000000000000/3954950991604190707909883))
    ((25000000000000000000/3954793911971511218235371)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25178) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25178 : ℝ)^2 / (mW 12589 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1027429/500000000000))/2) * ((1-firstRatio 25178) * √(1-firstRatio 25178) *
      sixthConstant (e1CovarianceRatio 25178 (mW 12589) (1/10^6) rowEps))) /
    (712/10000 - 25178*(1+1/10^6)*((1027429/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25178 (mW 12589) /
    ((1/10^5) * ((mW 12589 : ℝ)*25178*((mW 12589 : ℝ)+25178+1)))^2 +
  8*(mW 12589 : ℝ)*25178*(25178+2)*(25178+3) /
    ((1/1000)*((mW 12589 : ℝ)*25178*(25178+2)))^2 +
  covarianceVarianceBound 25178 (mW 12589) /
    ((1/1000)*covarianceMeanBound 25178 (mW 12589))^2 +
  normVarianceBound 25178 (mW 12589) / (3*inputVarianceMean 25178 (mW 12589))^2

end BstLean.Part268.WorldRow12589
namespace BstLean.Part268.WorldRow12590
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12590 = 223918540829768 := by
  have hu : mW 12590 ≤ 223918540829768 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12590 ≤ 223918540829767 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12590)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25180 ^ 2)
    ((2500000000000000000/395526515086954968723373))
    ((25000000000000000000/3955108071236870197559217)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25180) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25180 : ℝ)^2 / (mW 12590 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2054693/1000000000000))/2) * ((1-firstRatio 25180) * √(1-firstRatio 25180) *
      sixthConstant (e1CovarianceRatio 25180 (mW 12590) (1/10^6) rowEps))) /
    (712/10000 - 25180*(1+1/10^6)*((2054693/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25180 (mW 12590) /
    ((1/10^5) * ((mW 12590 : ℝ)*25180*((mW 12590 : ℝ)+25180+1)))^2 +
  8*(mW 12590 : ℝ)*25180*(25180+2)*(25180+3) /
    ((1/1000)*((mW 12590 : ℝ)*25180*(25180+2)))^2 +
  covarianceVarianceBound 25180 (mW 12590) /
    ((1/1000)*covarianceMeanBound 25180 (mW 12590))^2 +
  normVarianceBound 25180 (mW 12590) / (3*inputVarianceMean 25180 (mW 12590))^2

end BstLean.Part268.WorldRow12590
namespace BstLean.Part268.WorldRow12591
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12591 = 223980796009056 := by
  have hu : mW 12591 ≤ 223980796009056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12591 ≤ 223980796009055 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12591)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25182 ^ 2)
    ((25000000000000000000/3955579310134908666557577))
    ((25000000000000000000/3955422230502229176883063)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25182) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25182 : ℝ)^2 / (mW 12591 : ℝ)) * (1 + 1/10^6)^2 *
    √(((16051/7812500000))/2) * ((1-firstRatio 25182) * √(1-firstRatio 25182) *
      sixthConstant (e1CovarianceRatio 25182 (mW 12591) (1/10^6) rowEps))) /
    (712/10000 - 25182*(1+1/10^6)*((16051/7812500000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25182 (mW 12591) /
    ((1/10^5) * ((mW 12591 : ℝ)*25182*((mW 12591 : ℝ)+25182+1)))^2 +
  8*(mW 12591 : ℝ)*25182*(25182+2)*(25182+3) /
    ((1/1000)*((mW 12591 : ℝ)*25182*(25182+2)))^2 +
  covarianceVarianceBound 25182 (mW 12591) /
    ((1/1000)*covarianceMeanBound 25182 (mW 12591))^2 +
  normVarianceBound 25182 (mW 12591) / (3*inputVarianceMean 25182 (mW 12591))^2

end BstLean.Part268.WorldRow12591
namespace BstLean.Part268.WorldRow12592
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12592 = 224043063550620 := by
  have hu : mW 12592 ≤ 224043063550620 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12592 ≤ 224043063550619 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12592)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25184 ^ 2)
    ((1562500000000000000/247243341837516727867589))
    ((25000000000000000000/3955736389767588156206909)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25184) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25184 : ℝ)^2 / (mW 12592 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2054363/1000000000000))/2) * ((1-firstRatio 25184) * √(1-firstRatio 25184) *
      sixthConstant (e1CovarianceRatio 25184 (mW 12592) (1/10^6) rowEps))) /
    (712/10000 - 25184*(1+1/10^6)*((2054363/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25184 (mW 12592) /
    ((1/10^5) * ((mW 12592 : ℝ)*25184*((mW 12592 : ℝ)+25184+1)))^2 +
  8*(mW 12592 : ℝ)*25184*(25184+2)*(25184+3) /
    ((1/1000)*((mW 12592 : ℝ)*25184*(25184+2)))^2 +
  covarianceVarianceBound 25184 (mW 12592) /
    ((1/1000)*covarianceMeanBound 25184 (mW 12592))^2 +
  normVarianceBound 25184 (mW 12592) / (3*inputVarianceMean 25184 (mW 12592))^2

end BstLean.Part268.WorldRow12592
namespace BstLean.Part268.WorldRow12593
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12593 = 224105343455930 := by
  have hu : mW 12593 ≤ 224105343455930 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12593 ≤ 224105343455929 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12593)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25186 ^ 2)
    ((25000000000000000000/3956207628665626625205271))
    ((5000000000000000000/791210109806589427106151)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25186) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25186 : ℝ)^2 / (mW 12593 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1027099/500000000000))/2) * ((1-firstRatio 25186) * √(1-firstRatio 25186) *
      sixthConstant (e1CovarianceRatio 25186 (mW 12593) (1/10^6) rowEps))) /
    (712/10000 - 25186*(1+1/10^6)*((1027099/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25186 (mW 12593) /
    ((1/10^5) * ((mW 12593 : ℝ)*25186*((mW 12593 : ℝ)+25186+1)))^2 +
  8*(mW 12593 : ℝ)*25186*(25186+2)*(25186+3) /
    ((1/1000)*((mW 12593 : ℝ)*25186*(25186+2)))^2 +
  covarianceVarianceBound 25186 (mW 12593) /
    ((1/1000)*covarianceMeanBound 25186 (mW 12593))^2 +
  normVarianceBound 25186 (mW 12593) / (3*inputVarianceMean 25186 (mW 12593))^2

end BstLean.Part268.WorldRow12593
namespace BstLean.Part268.WorldRow12594
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12594 = 224167635726461 := by
  have hu : mW 12594 ≤ 224167635726461 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12594 ≤ 224167635726460 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12594)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25188 ^ 2)
    ((12500000000000000000/1978260893965492802264559))
    ((25000000000000000000/3956364708298306114854601)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25188) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25188 : ℝ)^2 / (mW 12594 : ℝ)) * (1 + 1/10^6)^2 *
    √(((1027017/500000000000))/2) * ((1-firstRatio 25188) * √(1-firstRatio 25188) *
      sixthConstant (e1CovarianceRatio 25188 (mW 12594) (1/10^6) rowEps))) /
    (712/10000 - 25188*(1+1/10^6)*((1027017/500000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25188 (mW 12594) /
    ((1/10^5) * ((mW 12594 : ℝ)*25188*((mW 12594 : ℝ)+25188+1)))^2 +
  8*(mW 12594 : ℝ)*25188*(25188+2)*(25188+3) /
    ((1/1000)*((mW 12594 : ℝ)*25188*(25188+2)))^2 +
  covarianceVarianceBound 25188 (mW 12594) /
    ((1/1000)*covarianceMeanBound 25188 (mW 12594))^2 +
  normVarianceBound 25188 (mW 12594) / (3*inputVarianceMean 25188 (mW 12594))^2

end BstLean.Part268.WorldRow12594
namespace BstLean.Part268.WorldRow12595
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12595 = 224229940363685 := by
  have hu : mW 12595 ≤ 224229940363685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12595 ≤ 224229940363684 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12595)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25190 ^ 2)
    ((5000000000000000000/791367189439268916770593))
    ((25000000000000000000/3956678867563665094178447)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25190) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25190 : ℝ)^2 / (mW 12595 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2053869/1000000000000))/2) * ((1-firstRatio 25190) * √(1-firstRatio 25190) *
      sixthConstant (e1CovarianceRatio 25190 (mW 12595) (1/10^6) rowEps))) /
    (712/10000 - 25190*(1+1/10^6)*((2053869/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25190 (mW 12595) /
    ((1/10^5) * ((mW 12595 : ℝ)*25190*((mW 12595 : ℝ)+25190+1)))^2 +
  8*(mW 12595 : ℝ)*25190*(25190+2)*(25190+3) /
    ((1/1000)*((mW 12595 : ℝ)*25190*(25190+2)))^2 +
  covarianceVarianceBound 25190 (mW 12595) /
    ((1/1000)*covarianceMeanBound 25190 (mW 12595))^2 +
  normVarianceBound 25190 (mW 12595) / (3*inputVarianceMean 25190 (mW 12595))^2

end BstLean.Part268.WorldRow12595
namespace BstLean.Part268.WorldRow12596
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12596 = 224292257369076 := by
  have hu : mW 12596 ≤ 224292257369076 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12596 ≤ 224292257369075 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12596)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25192 ^ 2)
    ((6250000000000000000/989287526615425890794203))
    ((25000000000000000000/3956993026829024073502293)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25192) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25192 : ℝ)^2 / (mW 12596 : ℝ)) * (1 + 1/10^6)^2 *
    √(((256713/125000000000))/2) * ((1-firstRatio 25192) * √(1-firstRatio 25192) *
      sixthConstant (e1CovarianceRatio 25192 (mW 12596) (1/10^6) rowEps))) /
    (712/10000 - 25192*(1+1/10^6)*((256713/125000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25192 (mW 12596) /
    ((1/10^5) * ((mW 12596 : ℝ)*25192*((mW 12596 : ℝ)+25192+1)))^2 +
  8*(mW 12596 : ℝ)*25192*(25192+2)*(25192+3) /
    ((1/1000)*((mW 12596 : ℝ)*25192*(25192+2)))^2 +
  covarianceVarianceBound 25192 (mW 12596) /
    ((1/1000)*covarianceMeanBound 25192 (mW 12596))^2 +
  normVarianceBound 25192 (mW 12596) / (3*inputVarianceMean 25192 (mW 12596))^2

end BstLean.Part268.WorldRow12596
namespace BstLean.Part268.WorldRow12597
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12597 = 224354586744105 := by
  have hu : mW 12597 ≤ 224354586744105 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12597 ≤ 224354586744104 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12597)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25194 ^ 2)
    ((25000000000000000000/3957464265727062542500659))
    ((25000000000000000000/3957307186094383052826139)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25194) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25194 : ℝ)^2 / (mW 12597 : ℝ)) * (1 + 1/10^6)^2 *
    √(((2053539/1000000000000))/2) * ((1-firstRatio 25194) * √(1-firstRatio 25194) *
      sixthConstant (e1CovarianceRatio 25194 (mW 12597) (1/10^6) rowEps))) /
    (712/10000 - 25194*(1+1/10^6)*((2053539/1000000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25194 (mW 12597) /
    ((1/10^5) * ((mW 12597 : ℝ)*25194*((mW 12597 : ℝ)+25194+1)))^2 +
  8*(mW 12597 : ℝ)*25194*(25194+2)*(25194+3) /
    ((1/1000)*((mW 12597 : ℝ)*25194*(25194+2)))^2 +
  covarianceVarianceBound 25194 (mW 12597) /
    ((1/1000)*covarianceMeanBound 25194 (mW 12597))^2 +
  normVarianceBound 25194 (mW 12597) / (3*inputVarianceMean 25194 (mW 12597))^2

end BstLean.Part268.WorldRow12597
namespace BstLean.Part268.WorldRow12598
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12598 = 224416928490247 := by
  have hu : mW 12598 ≤ 224416928490247 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12598 ≤ 224416928490246 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12598)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25196 ^ 2)
    ((12500000000000000000/1978889212496210760912253))
    ((5000000000000000000/791524269071948406429997)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25196) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25196 : ℝ)^2 / (mW 12598 : ℝ)) * (1 + 1/10^6)^2 *
    √(((16427/8000000000))/2) * ((1-firstRatio 25196) * √(1-firstRatio 25196) *
      sixthConstant (e1CovarianceRatio 25196 (mW 12598) (1/10^6) rowEps))) /
    (712/10000 - 25196*(1+1/10^6)*((16427/8000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25196 (mW 12598) /
    ((1/10^5) * ((mW 12598 : ℝ)*25196*((mW 12598 : ℝ)+25196+1)))^2 +
  8*(mW 12598 : ℝ)*25196*(25196+2)*(25196+3) /
    ((1/1000)*((mW 12598 : ℝ)*25196*(25196+2)))^2 +
  covarianceVarianceBound 25196 (mW 12598) /
    ((1/1000)*covarianceMeanBound 25196 (mW 12598))^2 +
  normVarianceBound 25196 (mW 12598) / (3*inputVarianceMean 25196 (mW 12598))^2

end BstLean.Part268.WorldRow12598
namespace BstLean.Part268.WorldRow12599
open Real MeasureTheory Set BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228 BstLean.Part218 BstLean.Part205 BstLean.Part214
open BstLean.Part157 BstLean.Part192
open BstLean.Part250 (bounds_div pi_bounds rowEps meanMajorantValue endpointPolynomial mean_majorant)
theorem width : mW 12599 = 224479282608974 := by
  have hu : mW 12599 ≤ 224479282608974 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬ mW 12599 ≤ 224479282608973 := by rw [mW_le_iff]; norm_num
  omega

theorem kap_bounds : Bounds (kap1 (2*12599)) (49372/100000) (4938/10000) :=
  kap1_window (by norm_num)

theorem cnsq_bounds : Bounds (BstLean.Part137.cN 25198 ^ 2)
    ((25000000000000000000/3958092584257780501148353))
    ((25000000000000000000/3957935504625101011473831)) := by
  obtain ⟨hl, hu⟩ := BstLean.Part159.cN_sq_window (N := 25198) (by norm_num)
  constructor
  · apply le_trans _ hl
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [pi_bounds.2]
  · apply le_trans hu
    rw [div_le_iff₀ (by positivity)]
    norm_num at ⊢
    nlinarith only [pi_bounds.1]

noncomputable def conditionalValue : ℝ :=
  ((4 * (25198 : ℝ)^2 / (mW 12599 : ℝ)) * (1 + 1/10^6)^2 *
    √(((205321/100000000000))/2) * ((1-firstRatio 25198) * √(1-firstRatio 25198) *
      sixthConstant (e1CovarianceRatio 25198 (mW 12599) (1/10^6) rowEps))) /
    (712/10000 - 25198*(1+1/10^6)*((205321/100000000000)))^2

noncomputable def statisticsPayment : ℝ :=
  traceVariance 25198 (mW 12599) /
    ((1/10^5) * ((mW 12599 : ℝ)*25198*((mW 12599 : ℝ)+25198+1)))^2 +
  8*(mW 12599 : ℝ)*25198*(25198+2)*(25198+3) /
    ((1/1000)*((mW 12599 : ℝ)*25198*(25198+2)))^2 +
  covarianceVarianceBound 25198 (mW 12599) /
    ((1/1000)*covarianceMeanBound 25198 (mW 12599))^2 +
  normVarianceBound 25198 (mW 12599) / (3*inputVarianceMean 25198 (mW 12599))^2

end BstLean.Part268.WorldRow12599
