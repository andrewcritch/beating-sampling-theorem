import BstLean.Part293EndpointInterface
import BstLean.Part293ScalarTools

namespace BstLean.Part293.Coarse
open Real BstLean.Part156 BstLean.Part203 BstLean.Part232 BstLean.Part236

theorem cell0_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (570404667 / 2000000000 : ℝ) (8623251 / 1000000000 : ℝ) (3172813999 / 2500000000 : ℝ) ≤ (-742578184627849 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((570404667 / 2000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (1160412824644676763 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (290103206161669191 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (8623251 / 1000000000 : ℝ) * (e - 1)))
  have hk : (153542801989627969 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (307085603983089923 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (8623251 / 1000000000 : ℝ) * (e - 1))
  have hlw : (691162099525993 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (276464840213847 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (2187 / 12800000 : ℝ) / ((3172813999 / 2500000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (807985969942230157 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1615971939896143289 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3280277797937197 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (1640138899999759 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (570404667 / 2000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (8623251 / 1000000000 : ℝ) * (e - 1) / (1 + (8623251 / 1000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((2187 / 12800000 : ℝ) * ((3172813999 / 2500000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-742578184627849 / 1000000000000000000 : ℝ)
  interval_num

theorem cell0_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (570404667 / 2000000000 : ℝ) (8623251 / 1000000000 : ℝ) (3172813999 / 2500000000 : ℝ)) ≤ (1315191945936939 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (36454218332183157 / 40000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell0_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-7022170493 / 10000000000 : ℝ) (7224901 / 5000000000 : ℝ) (3170091131 / 5000000000 : ℝ) ≤ (-171934327226207 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-7022170493 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (693286744708414817 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (693286744710414819 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (7224901 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-588228106530935681 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-294114053263549143 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (7224901 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-110823205429869 / 250000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-443292819716583 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (2187 / 12800000 : ℝ) / ((3170091131 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (401105924202826549 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (401105924211650311 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2174582593523903 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-2174582591491827 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-7022170493 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (7224901 / 5000000000 : ℝ) * (e - 1) / (1 + (7224901 / 5000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(2187 / 12800000 : ℝ) * ((3170091131 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-171934327226207 / 250000000000000000 : ℝ)
  interval_num

theorem cell0_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-7022170493 / 10000000000 : ℝ) (7224901 / 5000000000 : ℝ) (3170091131 / 5000000000 : ℝ)) ≤ (203951009040601 / 50000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (36704974487801391 / 40000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell0_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (570404667 / 2000000000 : ℝ)
  τm := (-7022170493 / 10000000000 : ℝ)
  vp := (8623251 / 1000000000 : ℝ)
  vm := (7224901 / 5000000000 : ℝ)
  bp := (3172813999 / 2500000000 : ℝ)
  bm := (3170091131 / 5000000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell0_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell0_1_minus_exponent.trans (by norm_num)

theorem cell0_1_payment : cell0_1.payment ≤ endpointIntercept + radiusPrice * (0 / 1 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell0_1_plus_tail cell0_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell1_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1419589521 / 5000000000 : ℝ) (43115341 / 5000000000 : ℝ) (12679424141 / 10000000000 : ℝ) ≤ (-46106496534411 / 62500000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1419589521 / 5000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (1159635582159983203 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (289908895540495801 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (43115341 / 5000000000 : ℝ) * (e - 1)))
  have hk : (305599747471542241 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (12223989899015049 / 40000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (43115341 / 5000000000 : ℝ) * (e - 1))
  have hlw : (687800968389939 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (687800969398563 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (6561 / 25600000 : ℝ) / ((12679424141 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (806467102406225881 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (32258684096482509 / 20000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (408015888917267 / 125000000000000000 : ℝ) ≤ la ∧ la ≤ (3264127113400407 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1419589521 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (43115341 / 5000000000 : ℝ) * (e - 1) / (1 + (43115341 / 5000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((6561 / 25600000 : ℝ) * ((12679424141 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-46106496534411 / 62500000000000000 : ℝ)
  interval_num

theorem cell1_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1419589521 / 5000000000 : ℝ) (43115341 / 5000000000 : ℝ) (12679424141 / 10000000000 : ℝ)) ≤ (2734978904407611 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (45595544907951717 / 50000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell1_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-878841723 / 1250000000 : ℝ) (7200641 / 5000000000 : ℝ) (634376151 / 1000000000 : ℝ) ≤ (-341959206072817 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-878841723 / 1250000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (69297711979693897 / 100000000000000000 : ℝ) ≤ e ∧ e ≤ (692977119798938971 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (7200641 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-184006657735749 / 312500000000000 : ℝ) ≤ k ∧ k ≤ (-117764260950111883 / 200000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (7200641 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-221125043490131 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-221125042488689 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (6561 / 25600000 : ℝ) / ((634376151 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (401559590005691197 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (200779795007248703 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2172933543364867 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-434586708266571 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-878841723 / 1250000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (7200641 / 5000000000 : ℝ) * (e - 1) / (1 + (7200641 / 5000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(6561 / 25600000 : ℝ) * ((634376151 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-341959206072817 / 500000000000000000 : ℝ)
  interval_num

theorem cell1_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-878841723 / 1250000000 : ℝ) (7200641 / 5000000000 : ℝ) (634376151 / 1000000000 : ℝ)) ≤ (1051390549390243 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (918062505851168937 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell1_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1419589521 / 5000000000 : ℝ)
  τm := (-878841723 / 1250000000 : ℝ)
  vp := (43115341 / 5000000000 : ℝ)
  vm := (7200641 / 5000000000 : ℝ)
  bp := (12679424141 / 10000000000 : ℝ)
  bm := (634376151 / 1000000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell1_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell1_1_minus_exponent.trans (by norm_num)

theorem cell1_1_payment : cell1_1.payment ≤ endpointIntercept + radiusPrice * (2187 / 12800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell1_1_plus_tail cell1_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell2_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (112924947 / 400000000 : ℝ) (86277319 / 10000000000 : ℝ) (6332658187 / 5000000000 : ℝ) ≤ (-730427048215031 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((112924947 / 400000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (1158664761055563719 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (28966619026439093 / 25000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (86277319 / 10000000000 : ℝ) * (e - 1)))
  have hk : (75935890646009129 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (303743562587870501 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (86277319 / 10000000000 : ℝ) * (e - 1))
  have hlw : (1367980906670311 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1367980908687569 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (19683 / 51200000 : ℝ) / ((6332658187 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (321863195616948351 / 200000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1609315978096407111 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3244889791911343 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (324488979397357 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (112924947 / 400000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (86277319 / 10000000000 : ℝ) * (e - 1) / (1 + (86277319 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((19683 / 51200000 : ℝ) * ((6332658187 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-730427048215031 / 1000000000000000000 : ℝ)
  interval_num

theorem cell2_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (112924947 / 400000000 : ℝ) (86277319 / 10000000000 : ℝ) (6332658187 / 5000000000 : ℝ)) ≤ (2898921853848109 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (912740760662422569 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell2_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6996480623 / 10000000000 : ℝ) (14401507 / 10000000000 : ℝ) (6365088303 / 10000000000 : ℝ) ≤ (-678205453358659 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6996480623 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (86777056203908487 / 125000000000000000 : ℝ) ≤ e ∧ e ≤ (694216449633267897 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (14401507 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-293221711560624253 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-117288684623482227 / 200000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (14401507 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-440471388392127 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-110117846597311 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (19683 / 51200000 : ℝ) / ((6365088303 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (404268076986898497 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (202134038497834417 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2163088399230247 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-432617679439673 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6996480623 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (14401507 / 10000000000 : ℝ) * (e - 1) / (1 + (14401507 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(19683 / 51200000 : ℝ) * ((6365088303 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-678205453358659 / 1000000000000000000 : ℝ)
  interval_num

theorem cell2_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6996480623 / 10000000000 : ℝ) (14401507 / 10000000000 : ℝ) (6365088303 / 10000000000 : ℝ)) ≤ (4402231855388241 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (114839793331904863 / 125000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell2_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (112924947 / 400000000 : ℝ)
  τm := (-6996480623 / 10000000000 : ℝ)
  vp := (86277319 / 10000000000 : ℝ)
  vm := (14401507 / 10000000000 : ℝ)
  bp := (6332658187 / 5000000000 : ℝ)
  bm := (6365088303 / 10000000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell2_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell2_1_minus_exponent.trans (by norm_num)

theorem cell2_1_payment : cell2_1.payment ≤ endpointIntercept + radiusPrice * (6561 / 25600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell2_1_plus_tail cell2_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell3_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1405139691 / 5000000000 : ℝ) (86520107 / 10000000000 : ℝ) (395527493 / 312500000 : ℝ) ≤ (-1124362003877 / 1562500000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1405139691 / 5000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (1157888689420811273 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (578944344711405637 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (86520107 / 10000000000 : ℝ) * (e - 1)))
  have hk : (302258735863267961 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (151129367933550973 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (86520107 / 10000000000 : ℝ) * (e - 1))
  have hlw : (1365122425515641 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1365122427532947 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (59049 / 102400000 : ℝ) / ((395527493 / 312500000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (50223569710078897 / 31250000000000000 : ℝ) ≤ ea ∧ ea ≤ (160715423073419709 / 100000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (1616698038909973 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (323339607988221 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1405139691 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (86520107 / 10000000000 : ℝ) * (e - 1) / (1 + (86520107 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((59049 / 102400000 : ℝ) * ((395527493 / 312500000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-1124362003877 / 1562500000000000 : ℝ)
  interval_num

theorem cell3_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1405139691 / 5000000000 : ℝ) (86520107 / 10000000000 : ℝ) (395527493 / 312500000 : ℝ)) ≤ (98794426911483 / 31250000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (913977833226897977 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell3_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-3486465787 / 5000000000 : ℝ) (574333 / 400000000 : ℝ) (3193775321 / 5000000000 : ℝ) ≤ (-669669751014583 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-3486465787 / 5000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (347534887193827819 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (17376744359741391 / 25000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (574333 / 400000000 : ℝ) * (e - 1)))
  have hk : (-5848053947938251 / 10000000000000000 : ℝ) ≤ k ∧ k ≤ (-584805394789987747 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (574333 / 400000000 : ℝ) * (e - 1))
  have hlw : (-437924604149711 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-87584920429367 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (59049 / 102400000 : ℝ) / ((3193775321 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (8142613294114669 / 20000000000000000 : ℝ) ≤ ea ∧ ea ≤ (407130664714456263 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-107634160799597 / 50000000000000000 : ℝ) ≤ la ∧ la ≤ (-2152683213960231 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-3486465787 / 5000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (574333 / 400000000 : ℝ) * (e - 1) / (1 + (574333 / 400000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(59049 / 102400000 : ℝ) * ((3193775321 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-669669751014583 / 1000000000000000000 : ℝ)
  interval_num

theorem cell3_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-3486465787 / 5000000000 : ℝ) (574333 / 400000000 : ℝ) (3193775321 / 5000000000 : ℝ)) ≤ (4713342284596927 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (459849554036651389 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell3_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1405139691 / 5000000000 : ℝ)
  τm := (-3486465787 / 5000000000 : ℝ)
  vp := (86520107 / 10000000000 : ℝ)
  vm := (574333 / 400000000 : ℝ)
  bp := (395527493 / 312500000 : ℝ)
  bm := (3193775321 / 5000000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell3_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell3_1_minus_exponent.trans (by norm_num)

theorem cell3_1_payment : cell3_1.payment ≤ endpointIntercept + radiusPrice * (19683 / 51200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell3_1_plus_tail cell3_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell4_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1385371521 / 5000000000 : ℝ) (43285677 / 5000000000 : ℝ) (394411667 / 312500000 : ℝ) ≤ (-175871976331197 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1385371521 / 5000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (231100620992141079 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (288875776240676349 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (43285677 / 5000000000 : ℝ) * (e - 1)))
  have hk : (297697723124174967 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (37212215391001119 / 125000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (43285677 / 5000000000 : ℝ) * (e - 1))
  have hlw : (1345306103571167 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1345306105588483 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (177147 / 204800000 : ℝ) / ((394411667 / 312500000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1598021508119962923 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1598021508131610411 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3184837186910591 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3184837188972723 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1385371521 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (43285677 / 5000000000 : ℝ) * (e - 1) / (1 + (43285677 / 5000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((177147 / 204800000 : ℝ) * ((394411667 / 312500000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-175871976331197 / 250000000000000000 : ℝ)
  interval_num

theorem cell4_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1385371521 / 5000000000 : ℝ) (43285677 / 5000000000 : ℝ) (394411667 / 312500000 : ℝ)) ≤ (719221518673967 / 200000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (915819498134129789 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell4_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6926368683 / 10000000000 : ℝ) (3577539 / 2500000000 : ℝ) (1606215687 / 2500000000 : ℝ) ≤ (-656946847618161 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6926368683 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (348380059357834879 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (1088687685496359 / 1562500000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (3577539 / 2500000000 : ℝ) * (e - 1)))
  have hk : (-72695166738969619 / 125000000000000000 : ℝ) ≤ k ∧ k ≤ (-145390333476979907 / 250000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3577539 / 2500000000 : ℝ) * (e - 1))
  have hlw : (-434035181302643 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-217017589649889 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (177147 / 204800000 : ℝ) / ((1606215687 / 2500000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (205954059361400997 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (411908118731452511 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2135317951025887 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-1067658974497221 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6926368683 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3577539 / 2500000000 : ℝ) * (e - 1) / (1 + (3577539 / 2500000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(177147 / 204800000 : ℝ) * ((1606215687 / 2500000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-656946847618161 / 1000000000000000000 : ℝ)
  interval_num

theorem cell4_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6926368683 / 10000000000 : ℝ) (3577539 / 2500000000 : ℝ) (1606215687 / 2500000000 : ℝ)) ≤ (521834602431491 / 100000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (921162927129772167 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell4_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1385371521 / 5000000000 : ℝ)
  τm := (-6926368683 / 10000000000 : ℝ)
  vp := (43285677 / 5000000000 : ℝ)
  vm := (3577539 / 2500000000 : ℝ)
  bp := (394411667 / 312500000 : ℝ)
  bm := (1606215687 / 2500000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell4_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell4_1_minus_exponent.trans (by norm_num)

theorem cell4_1_payment : cell4_1.payment ≤ endpointIntercept + radiusPrice * (59049 / 102400000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell4_1_plus_tail cell4_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell5_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (2655411993 / 10000000000 : ℝ) (3490549 / 400000000 : ℝ) (12523974371 / 10000000000 : ℝ) ≤ (-161202418260539 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2655411993 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (114857218480278753 / 100000000000000000 : ℝ) ≤ e ∧ e ≤ (1148572184804787531 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (3490549 / 400000000 : ℝ) * (e - 1)))
  have hk : (142221588382995619 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (142221588384912611 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3490549 / 400000000 : ℝ) * (e - 1))
  have hlw : (323914125303993 / 250000000000000000 : ℝ) ≤ lw ∧ lw ≤ (647828251616713 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (1594323 / 819200000 : ℝ) / ((12523974371 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (2458274766031533 / 1562500000000000 : ℝ) ≤ ea ∧ ea ≤ (1573295850271791249 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3053358474573759 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3053358476635691 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2655411993 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (3490549 / 400000000 : ℝ) * (e - 1) / (1 + (3490549 / 400000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((1594323 / 819200000 : ℝ) * ((12523974371 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-161202418260539 / 250000000000000000 : ℝ)
  interval_num

theorem cell5_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (2655411993 / 10000000000 : ℝ) (3490549 / 400000000 : ℝ) (12523974371 / 10000000000 : ℝ)) ≤ (287522437348181 / 50000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (230640381802444133 / 250000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell5_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6704793547 / 10000000000 : ℝ) (14192509 / 10000000000 : ℝ) (657851961 / 1000000000 : ℝ) ≤ (-610119228759991 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6704793547 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (176215080458537589 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (704860321836150357 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (14192509 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-566018023569273619 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-141504505891359103 / 250000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (14192509 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-418965008445671 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-418965006442829 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (1594323 / 819200000 : ℝ) / ((657851961 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (107969358521135189 / 250000000000000000 : ℝ) ≤ ea ∧ ea ≤ (431877434092925497 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2062736015986481 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-515684003489001 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6704793547 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (14192509 / 10000000000 : ℝ) * (e - 1) / (1 + (14192509 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(1594323 / 819200000 : ℝ) * ((657851961 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-610119228759991 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6704793547 / 10000000000 : ℝ) (14192509 / 10000000000 : ℝ) (657851961 / 1000000000 : ℝ)) ≤ (7589771222356781 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (57910670133228177 / 62500000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell5_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2655411993 / 10000000000 : ℝ)
  τm := (-6704793547 / 10000000000 : ℝ)
  vp := (3490549 / 400000000 : ℝ)
  vm := (14192509 / 10000000000 : ℝ)
  bp := (12523974371 / 10000000000 : ℝ)
  bm := (657851961 / 1000000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell5_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell5_1_minus_exponent.trans (by norm_num)

theorem cell5_1_payment : cell5_1.payment ≤ endpointIntercept + radiusPrice * (177147 / 204800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell5_1_plus_tail cell5_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell6_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1186669637 / 5000000000 : ℝ) (3537359 / 400000000 : ℝ) (12276359029 / 10000000000 : ℝ) ≤ (-261276779613949 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1186669637 / 5000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (1131795450940707769 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (113179545094270777 / 100000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (3537359 / 400000000 : ℝ) * (e - 1)))
  have hk : (63089233656447013 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (252356934629622039 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3537359 / 400000000 : ℝ) * (e - 1))
  have hlw : (1164840869736737 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (582420435877213 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (14348907 / 3276800000 : ℝ) / ((12276359029 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (755599718075049971 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (302239887232315979 / 200000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (544616896636161 / 200000000000000000 : ℝ) ≤ la ∧ la ≤ (680771121310511 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1186669637 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (3537359 / 400000000 : ℝ) * (e - 1) / (1 + (3537359 / 400000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((14348907 / 3276800000 : ℝ) * ((12276359029 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-261276779613949 / 500000000000000000 : ℝ)
  interval_num

theorem cell6_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1186669637 / 5000000000 : ℝ) (3537359 / 400000000 : ℝ) (12276359029 / 10000000000 : ℝ)) ≤ (15291953961868689 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (468384201975765619 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell6_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6233419539 / 10000000000 : ℝ) (6918381 / 5000000000 : ℝ) (34517833 / 50000000 : ℝ) ≤ (-51001217632801 / 100000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6233419539 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (722407141503125437 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (361203570752562719 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (6918381 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-133087065329400473 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (-66543532664220619 / 125000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (6918381 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-384172417365849 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-192086207681539 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (14348907 / 3276800000 : ℝ) / ((34517833 / 50000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (237842987852793957 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (118921493928362409 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-380704947558981 / 200000000000000000 : ℝ) ≤ la ∧ la ≤ (-475881183941583 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6233419539 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (6918381 / 5000000000 : ℝ) * (e - 1) / (1 + (6918381 / 5000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(14348907 / 3276800000 : ℝ) * ((34517833 / 50000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-51001217632801 / 100000000000000000 : ℝ)
  interval_num

theorem cell6_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-6233419539 / 10000000000 : ℝ) (6918381 / 5000000000 : ℝ) (34517833 / 50000000 : ℝ)) ≤ (845290938364553 / 50000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (938238102058764247 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell6_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1186669637 / 5000000000 : ℝ)
  τm := (-6233419539 / 10000000000 : ℝ)
  vp := (3537359 / 400000000 : ℝ)
  vm := (6918381 / 5000000000 : ℝ)
  bp := (12276359029 / 10000000000 : ℝ)
  bm := (34517833 / 50000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell6_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell6_1_minus_exponent.trans (by norm_num)

theorem cell6_1_payment : cell6_1.payment ≤ endpointIntercept + radiusPrice * (1594323 / 819200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell6_1_plus_tail cell6_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell7_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (531711897 / 2500000000 : ℝ) (89551539 / 10000000000 : ℝ) (3014419581 / 2500000000 : ℝ) ≤ (-52995020371051 / 125000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((531711897 / 2500000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (1117335714647391227 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (279333928662347807 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (89551539 / 10000000000 : ℝ) * (e - 1)))
  have hk : (56173933918905561 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (224695735679456231 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (89551539 / 10000000000 : ℝ) * (e - 1))
  have hlw : (105020772040209 / 100000000000000000 : ℝ) ≤ lw ∧ lw ≤ (525103861210001 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (43046721 / 6553600000 : ℝ) / ((3014419581 / 2500000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1457423448063511777 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (145742344807487883 / 100000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2436976419339433 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (243697642140007 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (531711897 / 2500000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (89551539 / 10000000000 : ℝ) * (e - 1) / (1 + (89551539 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((43046721 / 6553600000 : ℝ) * ((3014419581 / 2500000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-52995020371051 / 125000000000000000 : ℝ)
  interval_num

theorem cell7_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (531711897 / 2500000000 : ℝ) (89551539 / 10000000000 : ℝ) (3014419581 / 2500000000 : ℝ)) ≤ (16826024996956183 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (948384735075621363 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell7_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-1446036963 / 2500000000 : ℝ) (3375413 / 2500000000 : ℝ) (898982887 / 1250000000 : ℝ) ≤ (-426471324281103 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1446036963 / 2500000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (184884404394970443 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (369768808790940887 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (3375413 / 2500000000 : ℝ) * (e - 1)))
  have hk : (-249740210825045861 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-49948042164625503 / 100000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3375413 / 2500000000 : ℝ) * (e - 1))
  have hlw : (-351729095078921 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-175864546538109 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (43046721 / 6553600000 : ℝ) / ((898982887 / 1250000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (258160779627575921 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (32270097453912961 / 62500000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-438966861524157 / 250000000000000000 : ℝ) ≤ la ∧ la ≤ (-54870857627173 / 31250000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1446036963 / 2500000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3375413 / 2500000000 : ℝ) * (e - 1) / (1 + (3375413 / 2500000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(43046721 / 6553600000 : ℝ) * ((898982887 / 1250000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-426471324281103 / 1000000000000000000 : ℝ)
  interval_num

theorem cell7_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-1446036963 / 2500000000 : ℝ) (3375413 / 2500000000 : ℝ) (898982887 / 1250000000 : ℝ)) ≤ (16491374790173553 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (474043544205477941 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell7_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (531711897 / 2500000000 : ℝ)
  τm := (-1446036963 / 2500000000 : ℝ)
  vp := (89551539 / 10000000000 : ℝ)
  vm := (3375413 / 2500000000 : ℝ)
  bp := (3014419581 / 2500000000 : ℝ)
  bm := (898982887 / 1250000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell7_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell7_1_minus_exponent.trans (by norm_num)

theorem cell7_1_payment : cell7_1.payment ≤ endpointIntercept + radiusPrice * (14348907 / 3276800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell7_1_plus_tail cell7_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell8_1_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1687030893 / 10000000000 : ℝ) (91567507 / 10000000000 : ℝ) (11658895019 / 10000000000 : ℝ) ≤ (-272306361175813 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1687030893 / 10000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (545996235716782439 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (1091992471435564879 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (91567507 / 10000000000 : ℝ) * (e - 1)))
  have hk : (176200573931663909 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (88100286967748949 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (91567507 / 10000000000 : ℝ) * (e - 1))
  have hlw : (210499386686863 / 250000000000000000 : ℝ) ≤ lw ∧ lw ≤ (841997548765767 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (105401599641 / 10000000000000 : ℝ) / ((11658895019 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (680961252027646753 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1361922504066447493 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (964337182596553 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (385734873450521 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1687030893 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (91567507 / 10000000000 : ℝ) * (e - 1) / (1 + (91567507 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * ((105401599641 / 10000000000000 : ℝ) * ((11658895019 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-272306361175813 / 1000000000000000000 : ℝ)
  interval_num

theorem cell8_1_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (1687030893 / 10000000000 : ℝ) (91567507 / 10000000000 : ℝ) (11658895019 / 10000000000 : ℝ)) ≤ (2830419504649463 / 25000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_1_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (193306898069882297 / 200000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell8_1_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-2444140253 / 5000000000 : ℝ) (12900963 / 10000000000 : ℝ) (7714082537 / 10000000000 : ℝ) ≤ (-145949747689787 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-2444140253 / 5000000000 : ℝ) * (5341697 / 10240000 : ℝ))
  have he : (774918667471571601 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (387459333736785801 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((5341697 / 10240000 : ℝ) * (1 + (12900963 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-215802422806809437 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-215802422804891327 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (12900963 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-290418762740411 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-290418760737827 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (105401599641 / 10000000000000 : ℝ) / ((7714082537 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (297097411742077113 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (594194823490992811 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1472960715246517 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-736480356610837 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-2444140253 / 5000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (12900963 / 10000000000 : ℝ) * (e - 1) / (1 + (12900963 / 10000000000 : ℝ) * (e - 1))) / (5341697 / 10240000 : ℝ) + k * (-(105401599641 / 10000000000000 : ℝ) * ((7714082537 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-145949747689787 / 500000000000000000 : ℝ)
  interval_num

theorem cell8_1_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (5341697 / 10240000 : ℝ) agentFrame (-2444140253 / 5000000000 : ℝ) (12900963 / 10000000000 : ℝ) (7714082537 / 10000000000 : ℝ)) ≤ (6049469569716767 / 62500000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_1_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (120521275845789813 / 125000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell8_1 : EndCertificate 8000 (5341697 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1687030893 / 10000000000 : ℝ)
  τm := (-2444140253 / 5000000000 : ℝ)
  vp := (91567507 / 10000000000 : ℝ)
  vm := (12900963 / 10000000000 : ℝ)
  bp := (11658895019 / 10000000000 : ℝ)
  bm := (7714082537 / 10000000000 : ℝ)
  τp_pos := by norm_num
  τm_neg := by norm_num
  vp_nonneg := by norm_num
  vp_le_one := by norm_num
  vm_nonneg := by norm_num
  vm_le_one := by norm_num
  bp_pos := by norm_num
  bm_pos := by norm_num
  root_guard := by
    have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ √(1 / 100 / aL) := le_sqrt_of_sq_le (by norm_num [aL])
    norm_num [rootAllowance, samplingDeviation] at hu ⊢
    linarith
  plus_nonpos := cell8_1_plus_exponent.trans (by norm_num)
  minus_nonpos := cell8_1_minus_exponent.trans (by norm_num)

theorem cell8_1_payment : cell8_1.payment ≤ endpointIntercept + radiusPrice * (43046721 / 6553600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (12977 / 409600 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell8_1_plus_tail cell8_1_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

end BstLean.Part293.Coarse
