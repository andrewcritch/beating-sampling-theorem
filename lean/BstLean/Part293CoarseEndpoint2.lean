import BstLean.Part293EndpointInterface
import BstLean.Part293ScalarTools

namespace BstLean.Part293.Coarse
open Real BstLean.Part156 BstLean.Part203 BstLean.Part232 BstLean.Part236

theorem cell0_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (538574903 / 2000000000 : ℝ) (84394109 / 10000000000 : ℝ) (784687083 / 625000000 : ℝ) ≤ (-351113930879387 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((538574903 / 2000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (296475912108979551 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (237180729687583641 / 200000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (84394109 / 10000000000 : ℝ) * (e - 1)))
  have hk : (293147320021107457 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (73286830006066539 / 250000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (84394109 / 10000000000 : ℝ) * (e - 1))
  have hlw : (97980488189587 / 62500000000000000 : ℝ) ≤ lw ∧ lw ≤ (48990244157821 / 31250000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (2187 / 12800000 : ℝ) / ((784687083 / 625000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (790582519039055573 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (395291259521979243 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (48362574447813 / 15625000000000000 : ℝ) ≤ la ∧ la ≤ (154760238335617 / 50000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (538574903 / 2000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (84394109 / 10000000000 : ℝ) * (e - 1) / (1 + (84394109 / 10000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((2187 / 12800000 : ℝ) * ((784687083 / 625000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-351113930879387 / 500000000000000000 : ℝ)
  interval_num

theorem cell0_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (538574903 / 2000000000 : ℝ) (84394109 / 10000000000 : ℝ) (784687083 / 625000000 : ℝ)) ≤ (3632540933127769 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (183192751210563411 / 200000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell0_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-1350592411 / 2000000000 : ℝ) (15340041 / 10000000000 : ℝ) (653170889 / 1000000000 : ℝ) ≤ (-657357328211973 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1350592411 / 2000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (326043235052043653 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (163021617526521827 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (15340041 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-109954247917352927 / 200000000000000000 : ℝ) ≤ k ∧ k ≤ (-68721404947950319 / 125000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (15340041 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-53384325126057 / 100000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-266921624628749 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (2187 / 12800000 : ℝ) / ((653170889 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (425743595983084219 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (425743595990614681 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2085029952284821 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-260628743782181 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1350592411 / 2000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (15340041 / 10000000000 : ℝ) * (e - 1) / (1 + (15340041 / 10000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(2187 / 12800000 : ℝ) * ((653170889 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-657357328211973 / 1000000000000000000 : ℝ)
  interval_num

theorem cell0_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-1350592411 / 2000000000 : ℝ) (15340041 / 10000000000 : ℝ) (653170889 / 1000000000 : ℝ)) ≤ (520123789171641 / 100000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (921115663404169493 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell0_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (538574903 / 2000000000 : ℝ)
  τm := (-1350592411 / 2000000000 : ℝ)
  vp := (84394109 / 10000000000 : ℝ)
  vm := (15340041 / 10000000000 : ℝ)
  bp := (784687083 / 625000000 : ℝ)
  bm := (653170889 / 1000000000 : ℝ)
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
  plus_nonpos := cell0_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell0_2_minus_exponent.trans (by norm_num)

theorem cell0_2_payment : cell0_2.payment ≤ endpointIntercept + radiusPrice * (0 / 1 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell0_2_plus_tail cell0_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell1_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2693944873 / 10000000000 : ℝ) (1692063 / 200000000 : ℝ) (12558864701 / 10000000000 : ℝ) ≤ (-34881107749503 / 50000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2693944873 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (1185984022203716463 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (74124001387857279 / 62500000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (1692063 / 200000000 : ℝ) * (e - 1)))
  have hk : (18329545162429001 / 62500000000000000 : ℝ) ≤ k ∧ k ≤ (58654544520404543 / 200000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (1692063 / 200000000 : ℝ) * (e - 1))
  have hlw : (1572246783824357 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (2456635602877 / 1562500000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (6561 / 25600000 : ℝ) / ((12558864701 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1582148578050754371 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (158214857806057231 / 100000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3100434850813813 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (620086970573237 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2693944873 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (1692063 / 200000000 : ℝ) * (e - 1) / (1 + (1692063 / 200000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((6561 / 25600000 : ℝ) * ((12558864701 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-34881107749503 / 50000000000000000 : ℝ)
  interval_num

theorem cell1_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2693944873 / 10000000000 : ℝ) (1692063 / 200000000 : ℝ) (12558864701 / 10000000000 : ℝ)) ≤ (75377612364743 / 20000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (458245620218520337 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell1_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-1350592411 / 2000000000 : ℝ) (15301749 / 10000000000 : ℝ) (6537771957 / 10000000000 : ℝ) ≤ (-163420147831263 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1350592411 / 2000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (326043235052043653 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (163021617526521827 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (15301749 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-549770506774631327 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-549770506771469251 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (15301749 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-66563788783517 / 125000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-33281894266567 / 62500000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (6561 / 25600000 : ℝ) / ((6537771957 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (426535584709471001 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (213267792358493319 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1041075688266833 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (-1041075687253173 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1350592411 / 2000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (15301749 / 10000000000 : ℝ) * (e - 1) / (1 + (15301749 / 10000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(6561 / 25600000 : ℝ) * ((6537771957 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-163420147831263 / 250000000000000000 : ℝ)
  interval_num

theorem cell1_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-1350592411 / 2000000000 : ℝ) (15301749 / 10000000000 : ℝ) (6537771957 / 10000000000 : ℝ)) ≤ (1339124694318901 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (184307819638490927 / 200000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell1_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2693944873 / 10000000000 : ℝ)
  τm := (-1350592411 / 2000000000 : ℝ)
  vp := (1692063 / 200000000 : ℝ)
  vm := (15301749 / 10000000000 : ℝ)
  bp := (12558864701 / 10000000000 : ℝ)
  bm := (6537771957 / 10000000000 : ℝ)
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
  plus_nonpos := cell1_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell1_2_minus_exponent.trans (by norm_num)

theorem cell1_2_payment : cell1_2.payment ≤ endpointIntercept + radiusPrice * (2187 / 12800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell1_2_plus_tail cell1_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell2_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2681100579 / 10000000000 : ℝ) (84693587 / 10000000000 : ℝ) (196063257 / 156250000 : ℝ) ≤ (-138149922261859 / 200000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2681100579 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (148127487069343501 / 125000000000000000 : ℝ) ≤ e ∧ e ≤ (118501989655674801 / 100000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (84693587 / 10000000000 : ℝ) * (e - 1)))
  have hk : (291754309910977493 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (145877154957068097 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (84693587 / 10000000000 : ℝ) * (e - 1))
  have hlw : (1565773406339843 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1565773408356783 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (19683 / 51200000 : ℝ) / ((196063257 / 156250000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (315880289082351487 / 200000000000000000 : ℝ) ≤ ea ∧ ea ≤ (49356295169424147 / 31250000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3085826590703309 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3085826592755667 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2681100579 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (84693587 / 10000000000 : ℝ) * (e - 1) / (1 + (84693587 / 10000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((19683 / 51200000 : ℝ) * ((196063257 / 156250000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-138149922261859 / 200000000000000000 : ℝ)
  interval_num

theorem cell2_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2681100579 / 10000000000 : ℝ) (84693587 / 10000000000 : ℝ) (196063257 / 156250000 : ℝ)) ≤ (3981897197776369 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (57329931686156921 / 62500000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell2_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-52515001 / 78125000 : ℝ) (3058473 / 2000000000 : ℝ) (655705783 / 1000000000 : ℝ) ≤ (-648183004945389 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-52515001 / 78125000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (326684698454085089 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (32668469845508509 / 50000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (3058473 / 2000000000 : ℝ) * (e - 1)))
  have hk : (-547741980775096941 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-3423387379824593 / 6250000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3058473 / 2000000000 : ℝ) * (e - 1))
  have hlw : (-530220713426431 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-66277588927921 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (19683 / 51200000 : ℝ) / ((655705783 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (53632465032179733 / 125000000000000000 : ℝ) ≤ ea ∧ ea ≤ (107264930066231701 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-64780536426543 / 31250000000000000 : ℝ) ≤ la ∧ la ≤ (-1036488581811077 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-52515001 / 78125000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3058473 / 2000000000 : ℝ) * (e - 1) / (1 + (3058473 / 2000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(19683 / 51200000 : ℝ) * ((655705783 / 1000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-648183004945389 / 1000000000000000000 : ℝ)
  interval_num

theorem cell2_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-52515001 / 78125000 : ℝ) (3058473 / 2000000000 : ℝ) (655705783 / 1000000000 : ℝ)) ≤ (2798669313194039 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (922172595936127789 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell2_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2681100579 / 10000000000 : ℝ)
  τm := (-52515001 / 78125000 : ℝ)
  vp := (84693587 / 10000000000 : ℝ)
  vm := (3058473 / 2000000000 : ℝ)
  bp := (196063257 / 156250000 : ℝ)
  bm := (655705783 / 1000000000 : ℝ)
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
  plus_nonpos := cell2_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell2_2_minus_exponent.trans (by norm_num)

theorem cell2_2_payment : cell2_2.payment ≤ endpointIntercept + radiusPrice * (6561 / 25600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell2_2_plus_tail cell2_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell3_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2655411993 / 10000000000 : ℝ) (42364923 / 5000000000 : ℝ) (500977081 / 400000000 : ℝ) ≤ (-680518017404063 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2655411993 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (14788674950979889 / 12500000000000000 : ℝ) ≤ e ∧ e ≤ (1183093996080391121 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (42364923 / 5000000000 : ℝ) * (e - 1)))
  have hk : (18045119074815751 / 62500000000000000 : ℝ) ≤ k ∧ k ≤ (57744381040042143 / 200000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (42364923 / 5000000000 : ℝ) * (e - 1))
  have hlw : (96884406485227 / 62500000000000000 : ℝ) ≤ lw ∧ lw ≤ (77507525289029 / 50000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (59049 / 102400000 : ℝ) / ((500977081 / 400000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1573410539030820773 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1573410539040622747 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (610793674428553 / 200000000000000000 : ℝ) ≤ la ∧ la ≤ (3053968374195053 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2655411993 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (42364923 / 5000000000 : ℝ) * (e - 1) / (1 + (42364923 / 5000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((59049 / 102400000 : ℝ) * ((500977081 / 400000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-680518017404063 / 1000000000000000000 : ℝ)
  interval_num

theorem cell3_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2655411993 / 10000000000 : ℝ) (42364923 / 5000000000 : ℝ) (500977081 / 400000000 : ℝ)) ≤ (13504803311413 / 3125000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (22961320266483989 / 25000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell3_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-6683385321 / 10000000000 : ℝ) (7632739 / 5000000000 : ℝ) (6583263377 / 10000000000 : ℝ) ≤ (-319985506358267 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6683385321 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (81870688470644787 / 125000000000000000 : ℝ) ≤ e ∧ e ≤ (327482753883579149 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (7632739 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-136304496468334069 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (-545217985870174237 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (7632739 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-105370081470133 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-65856300668451 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (59049 / 102400000 : ℝ) / ((6583263377 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (21625074637232219 / 50000000000000000 : ℝ) ≤ ea ∧ ea ≤ (216250746376047463 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2060467851596889 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-2060467849569807 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6683385321 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (7632739 / 5000000000 : ℝ) * (e - 1) / (1 + (7632739 / 5000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(59049 / 102400000 : ℝ) * ((6583263377 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-319985506358267 / 500000000000000000 : ℝ)
  interval_num

theorem cell3_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-6683385321 / 10000000000 : ℝ) (7632739 / 5000000000 : ℝ) (6583263377 / 10000000000 : ℝ)) ≤ (5977408885475749 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (923119691223096237 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell3_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2655411993 / 10000000000 : ℝ)
  τm := (-6683385321 / 10000000000 : ℝ)
  vp := (42364923 / 5000000000 : ℝ)
  vm := (7632739 / 5000000000 : ℝ)
  bp := (500977081 / 400000000 : ℝ)
  bm := (6583263377 / 10000000000 : ℝ)
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
  plus_nonpos := cell3_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell3_2_minus_exponent.trans (by norm_num)

theorem cell3_2_payment : cell3_2.payment ≤ endpointIntercept + radiusPrice * (19683 / 51200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell3_2_plus_tail cell3_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell4_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (1310312683 / 5000000000 : ℝ) (4242083 / 500000000 : ℝ) (12493262623 / 10000000000 : ℝ) ≤ (-665312115218597 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1310312683 / 5000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (118049099397351471 / 100000000000000000 : ℝ) ≤ e ∧ e ≤ (1180490993975514711 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (4242083 / 500000000 : ℝ) * (e - 1)))
  have hk : (142311455688553891 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (142311455690133241 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (4242083 / 500000000 : ℝ) * (e - 1))
  have hlw : (382536071320247 / 250000000000000000 : ℝ) ≤ lw ∧ lw ≤ (765072143648979 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (177147 / 204800000 : ℝ) / ((12493262623 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1565524422400091383 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1565524422409878753 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3012030327779823 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3012030329832033 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1310312683 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (4242083 / 500000000 : ℝ) * (e - 1) / (1 + (4242083 / 500000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((177147 / 204800000 : ℝ) * ((12493262623 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-665312115218597 / 1000000000000000000 : ℝ)
  interval_num

theorem cell4_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (1310312683 / 5000000000 : ℝ) (4242083 / 500000000 : ℝ) (12493262623 / 10000000000 : ℝ)) ≤ (4880552141930107 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (920200208756164037 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell4_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-3323897073 / 5000000000 : ℝ) (7595043 / 5000000000 : ℝ) (165377459 / 250000000 : ℝ) ≤ (-62773199495113 / 100000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-3323897073 / 5000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (41027697310114339 / 62500000000000000 : ℝ) ≤ e ∧ e ≤ (328221578481914713 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (7595043 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-542880396146363309 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-5428803961432013 / 10000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (7595043 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-522002019514209 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-2039070380903 / 3906250000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (177147 / 204800000 : ℝ) / ((165377459 / 250000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (109175301546255289 / 250000000000000000 : ℝ) ≤ ea ∧ ea ≤ (54587650774052267 / 125000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2045203970844607 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-51130099220443 / 25000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-3323897073 / 5000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (7595043 / 5000000000 : ℝ) * (e - 1) / (1 + (7595043 / 5000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(177147 / 204800000 : ℝ) * ((165377459 / 250000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-62773199495113 / 100000000000000000 : ℝ)
  interval_num

theorem cell4_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-3323897073 / 5000000000 : ℝ) (7595043 / 5000000000 : ℝ) (165377459 / 250000000 : ℝ)) ≤ (3296140171429159 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (924533031853808749 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell4_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1310312683 / 5000000000 : ℝ)
  τm := (-3323897073 / 5000000000 : ℝ)
  vp := (4242083 / 500000000 : ℝ)
  vm := (7595043 / 5000000000 : ℝ)
  bp := (12493262623 / 10000000000 : ℝ)
  bm := (165377459 / 250000000 : ℝ)
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
  plus_nonpos := cell4_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell4_2_minus_exponent.trans (by norm_num)

theorem cell4_2_payment : cell4_2.payment ≤ endpointIntercept + radiusPrice * (59049 / 102400000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell4_2_plus_tail cell4_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell5_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (100152903 / 400000000 : ℝ) (85465623 / 10000000000 : ℝ) (6195756217 / 5000000000 : ℝ) ≤ (-609888789201861 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((100152903 / 400000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (14647409246698003 / 12500000000000000 : ℝ) ≤ e ∧ e ≤ (1171792739737840241 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (85465623 / 10000000000 : ℝ) * (e - 1)))
  have hk : (270923376396330303 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (270923376399489003 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (85465623 / 10000000000 : ℝ) * (e - 1))
  have hlw : (733580272627067 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1467160547271229 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (1594323 / 819200000 : ℝ) / ((6195756217 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (15399180068180003 / 10000000000000000 : ℝ) ≤ ea ∧ ea ≤ (76995900341387577 / 50000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (1437922166496949 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (575168867009183 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (100152903 / 400000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (85465623 / 10000000000 : ℝ) * (e - 1) / (1 + (85465623 / 10000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((1594323 / 819200000 : ℝ) * ((6195756217 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-609888789201861 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (100152903 / 400000000 : ℝ) (85465623 / 10000000000 : ℝ) (6195756217 / 5000000000 : ℝ)) ≤ (7603775995619787 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (463298706167263447 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell5_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-805318893 / 1250000000 : ℝ) (938147 / 625000000 : ℝ) (6756228117 / 10000000000 : ℝ) ≤ (-582716171480061 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-805318893 / 1250000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (66502956653768211 / 100000000000000000 : ℝ) ≤ e ∧ e ≤ (10391086977182533 / 15625000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (938147 / 625000000 : ℝ) * (e - 1)))
  have hk : (-529302259293108899 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-52930225928994701 / 100000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (938147 / 625000000 : ℝ) * (e - 1))
  have hlw : (-100585772021187 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-502928858102929 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (1594323 / 819200000 : ℝ) / ((6756228117 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (455564802307343923 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (455564802314539593 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1976647004109037 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-395329400416577 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-805318893 / 1250000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (938147 / 625000000 : ℝ) * (e - 1) / (1 + (938147 / 625000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(1594323 / 819200000 : ℝ) * ((6756228117 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-582716171480061 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-805318893 / 1250000000 : ℝ) (938147 / 625000000 : ℝ) (6756228117 / 10000000000 : ℝ)) ≤ (4725052758249879 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (9297500230048283 / 10000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell5_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (100152903 / 400000000 : ℝ)
  τm := (-805318893 / 1250000000 : ℝ)
  vp := (85465623 / 10000000000 : ℝ)
  vm := (938147 / 625000000 : ℝ)
  bp := (6195756217 / 5000000000 : ℝ)
  bm := (6756228117 / 10000000000 : ℝ)
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
  plus_nonpos := cell5_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell5_2_minus_exponent.trans (by norm_num)

theorem cell5_2_payment : cell5_2.payment ≤ endpointIntercept + radiusPrice * (177147 / 204800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell5_2_plus_tail cell5_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell6_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2235221311 / 10000000000 : ℝ) (43373591 / 5000000000 : ℝ) (6076484939 / 5000000000 : ℝ) ≤ (-494378489279067 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2235221311 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (1152032500428640677 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (576016250215320339 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (43373591 / 5000000000 : ℝ) * (e - 1)))
  have hk : (239796535551500599 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (239796535554659301 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (43373591 / 5000000000 : ℝ) * (e - 1))
  have hlw : (131797019305551 / 100000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1317970195072861 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (14348907 / 3276800000 : ℝ) / ((6076484939 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1480734088111215367 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1480734088120871771 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2561007661593721 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (160062978977827 / 62500000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2235221311 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (43373591 / 5000000000 : ℝ) * (e - 1) / (1 + (43373591 / 5000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((14348907 / 3276800000 : ℝ) * ((6076484939 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-494378489279067 / 1000000000000000000 : ℝ)
  interval_num

theorem cell6_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2235221311 / 10000000000 : ℝ) (43373591 / 5000000000 : ℝ) (6076484939 / 5000000000 : ℝ)) ≤ (9579066879441491 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (470036704936028429 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell6_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-2984246373 / 5000000000 : ℝ) (1822737 / 1250000000 : ℝ) (3533846477 / 5000000000 : ℝ) ≤ (-486634247184067 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-2984246373 / 5000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (137058740986391883 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (85661713116744927 / 125000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (1822737 / 1250000000 : ℝ) * (e - 1)))
  have hk : (-99452023345345271 / 200000000000000000 : ℝ) ≤ k ∧ k ≤ (-248630058361782373 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (1822737 / 1250000000 : ℝ) * (e - 1))
  have hlw : (-91801355003217 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-91801354602633 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (14348907 / 3276800000 : ℝ) / ((3533846477 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (24930721447384403 / 50000000000000000 : ℝ) ≤ ea ∧ ea ≤ (498614428954478687 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1820207065713639 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-910103531844481 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-2984246373 / 5000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (1822737 / 1250000000 : ℝ) * (e - 1) / (1 + (1822737 / 1250000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(14348907 / 3276800000 : ℝ) * ((3533846477 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-486634247184067 / 1000000000000000000 : ℝ)
  interval_num

theorem cell6_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-2984246373 / 5000000000 : ℝ) (1822737 / 1250000000 : ℝ) (3533846477 / 5000000000 : ℝ)) ≤ (10191297002384589 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (117622983748321197 / 125000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell6_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2235221311 / 10000000000 : ℝ)
  τm := (-2984246373 / 5000000000 : ℝ)
  vp := (43373591 / 5000000000 : ℝ)
  vm := (1822737 / 1250000000 : ℝ)
  bp := (6076484939 / 5000000000 : ℝ)
  bm := (3533846477 / 5000000000 : ℝ)
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
  plus_nonpos := cell6_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell6_2_minus_exponent.trans (by norm_num)

theorem cell6_2_payment : cell6_2.payment ≤ endpointIntercept + radiusPrice * (1594323 / 819200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell6_2_plus_tail cell6_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell7_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2010044797 / 10000000000 : ℝ) (88112787 / 10000000000 : ℝ) (11953171833 / 10000000000 : ℝ) ≤ (-25075699769767 / 62500000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2010044797 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (567861950513836137 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (283930975257418069 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (88112787 / 10000000000 : ℝ) * (e - 1)))
  have hk : (214099732237131849 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (214099732240290553 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (88112787 / 10000000000 : ℝ) * (e - 1))
  have hlw : (239037319414129 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (119518659908827 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (43046721 / 6553600000 : ℝ) / ((11953171833 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (358019036604444623 / 250000000000000000 : ℝ) ≤ ea ∧ ea ≤ (716038073213683053 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2302091048156959 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (2302091050208103 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2010044797 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (88112787 / 10000000000 : ℝ) * (e - 1) / (1 + (88112787 / 10000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((43046721 / 6553600000 : ℝ) * ((11953171833 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-25075699769767 / 62500000000000000 : ℝ)
  interval_num

theorem cell7_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (2010044797 / 10000000000 : ℝ) (88112787 / 10000000000 : ℝ) (11953171833 / 10000000000 : ℝ)) ≤ (403691431015227 / 10000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (475542709853129171 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell7_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-1103014643 / 2000000000 : ℝ) (7095413 / 5000000000 : ℝ) (7345639387 / 10000000000 : ℝ) ≤ (-203300925770299 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1103014643 / 2000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (176313272475273919 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (352626544951547839 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (7095413 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-465703824717581247 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-465703824714419893 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (7095413 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-20917885595491 / 50000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-418357709906979 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (43046721 / 6553600000 : ℝ) / ((7345639387 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (538681333358148693 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (538681333364621209 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-209328519838643 / 125000000000000000 : ℝ) ≤ la ∧ la ≤ (-837314078342813 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1103014643 / 2000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (7095413 / 5000000000 : ℝ) * (e - 1) / (1 + (7095413 / 5000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(43046721 / 6553600000 : ℝ) * ((7345639387 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-203300925770299 / 500000000000000000 : ℝ)
  interval_num

theorem cell7_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-1103014643 / 2000000000 : ℝ) (7095413 / 5000000000 : ℝ) (7345639387 / 10000000000 : ℝ)) ≤ (151036012419933 / 3906250000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (950444763879352341 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell7_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2010044797 / 10000000000 : ℝ)
  τm := (-1103014643 / 2000000000 : ℝ)
  vp := (88112787 / 10000000000 : ℝ)
  vm := (7095413 / 5000000000 : ℝ)
  bp := (11953171833 / 10000000000 : ℝ)
  bm := (7345639387 / 10000000000 : ℝ)
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
  plus_nonpos := cell7_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell7_2_minus_exponent.trans (by norm_num)

theorem cell7_2_payment : cell7_2.payment ≤ endpointIntercept + radiusPrice * (14348907 / 3276800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell7_2_plus_tail cell7_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell8_2_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (803410479 / 5000000000 : ℝ) (45282629 / 5000000000 : ℝ) (1158699367 / 1000000000 : ℝ) ≤ (-257820810221831 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((803410479 / 5000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (1107094785738619431 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (138386848217577429 / 125000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (45282629 / 5000000000 : ℝ) * (e - 1)))
  have hk : (21122055119151859 / 125000000000000000 : ℝ) ≤ k ∧ k ≤ (21122055119546697 / 125000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (45282629 / 5000000000 : ℝ) * (e - 1))
  have hlw : (969436633509011 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (484718317763563 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (105401599641 / 10000000000000 : ℝ) / ((1158699367 / 1000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (67252766760788223 / 50000000000000000 : ℝ) ≤ ea ∧ ea ≤ (672527667612608917 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (229859038809613 / 125000000000000000 : ℝ) ≤ la ∧ la ≤ (459718078131833 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (803410479 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (45282629 / 5000000000 : ℝ) * (e - 1) / (1 + (45282629 / 5000000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * ((105401599641 / 10000000000000 : ℝ) * ((1158699367 / 1000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-257820810221831 / 1000000000000000000 : ℝ)
  interval_num

theorem cell8_2_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (803410479 / 5000000000 : ℝ) (45282629 / 5000000000 : ℝ) (1158699367 / 1000000000 : ℝ)) ≤ (127127281012244417 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_2_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (968286173828178897 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell8_2_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-4654663243 / 10000000000 : ℝ) (537679 / 400000000 : ℝ) (7837849821 / 10000000000 : ℝ) ≤ (-277951520967169 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-4654663243 / 10000000000 : ℝ) * (6483673 / 10240000 : ℝ))
  have he : (93092523057677981 / 125000000000000000 : ℝ) ≤ e ∧ e ≤ (744740184463423849 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((6483673 / 10240000 : ℝ) * (1 + (537679 / 400000000 : ℝ) * (e - 1)))
  have hk : (-403283399045829227 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-403283399042668351 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (537679 / 400000000 : ℝ) * (e - 1))
  have hlw : (-343178485898137 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-68635696779089 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (105401599641 / 10000000000000 : ℝ) / ((7837849821 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (153364404361133829 / 250000000000000000 : ℝ) ≤ ea ∧ ea ≤ (613457617450519491 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-701496511019823 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (-350748255004477 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-4654663243 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (537679 / 400000000 : ℝ) * (e - 1) / (1 + (537679 / 400000000 : ℝ) * (e - 1))) / (6483673 / 10240000 : ℝ) + k * (-(105401599641 / 10000000000000 : ℝ) * ((7837849821 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-277951520967169 / 1000000000000000000 : ℝ)
  interval_num

theorem cell8_2_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (6483673 / 10240000 : ℝ) agentFrame (-4654663243 / 10000000000 : ℝ) (537679 / 400000000 : ℝ) (7837849821 / 10000000000 : ℝ)) ≤ (27054375553361111 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_2_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (6036579379519871 / 6250000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell8_2 : EndCertificate 8000 (6483673 / 10240000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (803410479 / 5000000000 : ℝ)
  τm := (-4654663243 / 10000000000 : ℝ)
  vp := (45282629 / 5000000000 : ℝ)
  vm := (537679 / 400000000 : ℝ)
  bp := (1158699367 / 1000000000 : ℝ)
  bm := (7837849821 / 10000000000 : ℝ)
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
  plus_nonpos := cell8_2_plus_exponent.trans (by norm_num)
  minus_nonpos := cell8_2_minus_exponent.trans (by norm_num)

theorem cell8_2_payment : cell8_2.payment ≤ endpointIntercept + radiusPrice * (43046721 / 6553600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (1051137 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell8_2_plus_tail cell8_2_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

end BstLean.Part293.Coarse
