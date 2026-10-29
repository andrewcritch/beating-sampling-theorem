import BstLean.Part293EndpointInterface
import BstLean.Part293ScalarTools

namespace BstLean.Part293.Coarse
open Real BstLean.Part156 BstLean.Part203 BstLean.Part232 BstLean.Part236

theorem cell0_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (592400519 / 2000000000 : ℝ) (5468411 / 625000000 : ℝ) (12783961451 / 10000000000 : ℝ) ≤ (-771014694096907 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((592400519 / 2000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (1142812310489253469 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (1142812310491253471 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (5468411 / 625000000 : ℝ) * (e - 1)))
  have hk : (158242445990585279 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (79121222996402069 / 250000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (5468411 / 625000000 : ℝ) * (e - 1))
  have hlw : (1248750241153327 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (312187560792707 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (2187 / 12800000 : ℝ) / ((12783961451 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (204984353431519557 / 125000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1639874827465529829 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (1703676434581531 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (4259191089043 / 1250000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (592400519 / 2000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (5468411 / 625000000 : ℝ) * (e - 1) / (1 + (5468411 / 625000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((2187 / 12800000 : ℝ) * ((12783961451 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-771014694096907 / 1000000000000000000 : ℝ)
  interval_num

theorem cell0_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (592400519 / 2000000000 : ℝ) (5468411 / 625000000 : ℝ) (12783961451 / 10000000000 : ℝ)) ≤ (2095176349654147 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (908121737926938299 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell0_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-7218992369 / 10000000000 : ℝ) (3457313 / 2500000000 : ℝ) (6203163877 / 10000000000 : ℝ) ≤ (-141600001429391 / 200000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-7218992369 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (2889106475168729 / 4000000000000000 : ℝ) ≤ e ∧ e ≤ (722276618794182251 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (3457313 / 2500000000 : ℝ) * (e - 1)))
  have hk : (-154116432499709981 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (-61646572999439879 / 100000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3457313 / 2500000000 : ℝ) * (e - 1))
  have hlw : (-384144437528627 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-192072217762929 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (2187 / 12800000 : ℝ) / ((6203163877 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (383932598889472013 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (191966299449735587 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2237008683310343 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-2237008681273991 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-7218992369 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3457313 / 2500000000 : ℝ) * (e - 1) / (1 + (3457313 / 2500000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(2187 / 12800000 : ℝ) * ((6203163877 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-141600001429391 / 200000000000000000 : ℝ)
  interval_num

theorem cell0_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-7218992369 / 10000000000 : ℝ) (3457313 / 2500000000 : ℝ) (6203163877 / 10000000000 : ℝ)) ≤ (69372289111331 / 20000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (7150805546244483 / 7812500000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell0_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (592400519 / 2000000000 : ℝ)
  τm := (-7218992369 / 10000000000 : ℝ)
  vp := (5468411 / 625000000 : ℝ)
  vm := (3457313 / 2500000000 : ℝ)
  bp := (12783961451 / 10000000000 : ℝ)
  bm := (6203163877 / 10000000000 : ℝ)
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
  plus_nonpos := cell0_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell0_0_minus_exponent.trans (by norm_num)

theorem cell0_0_payment : cell0_0.payment ≤ endpointIntercept + radiusPrice * (0 / 1 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell0_0_plus_tail cell0_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell1_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (592400519 / 2000000000 : ℝ) (43846737 / 5000000000 : ℝ) (12786813299 / 10000000000 : ℝ) ≤ (-23936055847923 / 31250000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((592400519 / 2000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (1142812310489253469 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (1142812310491253471 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (43846737 / 5000000000 : ℝ) * (e - 1)))
  have hk : (316483994127655703 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (15824199706604671 / 50000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (43846737 / 5000000000 : ℝ) * (e - 1))
  have hlw : (250317440110139 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (312896800642059 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (6561 / 25600000 : ℝ) / ((12786813299 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1640612993956819967 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (410153248492552211 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3411276931355473 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3411276933426893 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (592400519 / 2000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (43846737 / 5000000000 : ℝ) * (e - 1) / (1 + (43846737 / 5000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((6561 / 25600000 : ℝ) * ((12786813299 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-23936055847923 / 31250000000000000 : ℝ)
  interval_num

theorem cell1_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (592400519 / 2000000000 : ℝ) (43846737 / 5000000000 : ℝ) (12786813299 / 10000000000 : ℝ)) ≤ (272718115908643 / 125000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (454348204816828947 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell1_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-898092401 / 1250000000 : ℝ) (13849333 / 10000000000 : ℝ) (6221830477 / 10000000000 : ℝ) ≤ (-88010874267153 / 125000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-898092401 / 1250000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (723392479046779599 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (723392479048779601 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (13849333 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-306994117853034961 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-306994117850814397 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (13849333 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-383156362823143 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-38315636082037 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (6561 / 25600000 : ℝ) / ((6221830477 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (96562498552091567 / 250000000000000000 : ℝ) ≤ ea ∧ ea ≤ (77249998843666559 / 200000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2228584581873497 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-139286536239829 / 62500000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-898092401 / 1250000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (13849333 / 10000000000 : ℝ) * (e - 1) / (1 + (13849333 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(6561 / 25600000 : ℝ) * ((6221830477 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-88010874267153 / 125000000000000000 : ℝ)
  interval_num

theorem cell1_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-898092401 / 1250000000 : ℝ) (13849333 / 10000000000 : ℝ) (6221830477 / 10000000000 : ℝ)) ≤ (3578913726275517 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (457875459275023949 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell1_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (592400519 / 2000000000 : ℝ)
  τm := (-898092401 / 1250000000 : ℝ)
  vp := (43846737 / 5000000000 : ℝ)
  vm := (13849333 / 10000000000 : ℝ)
  bp := (12786813299 / 10000000000 : ℝ)
  bm := (6221830477 / 10000000000 : ℝ)
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
  plus_nonpos := cell1_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell1_0_minus_exponent.trans (by norm_num)

theorem cell1_0_payment : cell1_0.payment ≤ endpointIntercept + radiusPrice * (2187 / 12800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell1_0_plus_tail cell1_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell2_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (588547231 / 2000000000 : ℝ) (87694487 / 10000000000 : ℝ) (12769341773 / 10000000000 : ℝ) ≤ (-7583939730483 / 10000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((588547231 / 2000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (1141820432654521461 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (1141820432656521463 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (87694487 / 10000000000 : ℝ) * (e - 1)))
  have hk : (314288635890494507 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (12571545435797289 / 40000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (87694487 / 10000000000 : ℝ) * (e - 1))
  have hlw : (1242914269717551 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (310728567933773 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (19683 / 51200000 : ℝ) / ((12769341773 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (818046688052709493 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1636093376118792093 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3387250590844437 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (1693625296457887 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (588547231 / 2000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (87694487 / 10000000000 : ℝ) * (e - 1) / (1 + (87694487 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((19683 / 51200000 : ℝ) * ((12769341773 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-7583939730483 / 10000000000000000 : ℝ)
  interval_num

theorem cell2_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (588547231 / 2000000000 : ℝ) (87694487 / 10000000000 : ℝ) (12769341773 / 10000000000 : ℝ)) ≤ (1158882656899169 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (113694439059428871 / 125000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell2_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-7159049337 / 10000000000 : ℝ) (13839297 / 10000000000 : ℝ) (6240868937 / 10000000000 : ℝ) ≤ (-698234576066819 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-7159049337 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (90528813177510163 / 125000000000000000 : ℝ) ≤ e ∧ e ≤ (362115252711040653 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (13839297 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-612127180733925993 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-306063590364742439 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (13839297 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-381718440117439 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-95429609528667 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (19683 / 51200000 : ℝ) / ((6240868937 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (48577595934739219 / 125000000000000000 : ℝ) ≤ ea ∧ ea ≤ (388620767487838583 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-221996651651177 / 100000000000000000 : ℝ) ≤ la ∧ la ≤ (-2219966514475689 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-7159049337 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (13839297 / 10000000000 : ℝ) * (e - 1) / (1 + (13839297 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(19683 / 51200000 : ℝ) * ((6240868937 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-698234576066819 / 1000000000000000000 : ℝ)
  interval_num

theorem cell2_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-7159049337 / 10000000000 : ℝ) (13839297 / 10000000000 : ℝ) (6240868937 / 10000000000 : ℝ)) ≤ (937615160699139 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (45821054165169657 / 50000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell2_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (588547231 / 2000000000 : ℝ)
  τm := (-7159049337 / 10000000000 : ℝ)
  vp := (87694487 / 10000000000 : ℝ)
  vm := (13839297 / 10000000000 : ℝ)
  bp := (12769341773 / 10000000000 : ℝ)
  bm := (6240868937 / 10000000000 : ℝ)
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
  plus_nonpos := cell2_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell2_0_minus_exponent.trans (by norm_num)

theorem cell2_0_payment : cell2_0.payment ≤ endpointIntercept + radiusPrice * (6561 / 25600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell2_0_plus_tail cell2_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell3_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (2917047569 / 10000000000 : ℝ) (17549061 / 2000000000 : ℝ) (199167779 / 156250000 : ℝ) ≤ (-747124985277403 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2917047569 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (570249633961540721 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (1140499267925081443 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (17549061 / 2000000000 : ℝ) * (e - 1)))
  have hk : (38920522518687081 / 125000000000000000 : ℝ) ≤ k ∧ k ≤ (311364180153934363 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (17549061 / 2000000000 : ℝ) * (e - 1))
  have hlw : (1232055818049853 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (308013955016851 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (59049 / 102400000 : ℝ) / ((199167779 / 156250000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (815127789017902821 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1630255578049161549 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3356215934736123 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3356215936807367 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2917047569 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (17549061 / 2000000000 : ℝ) * (e - 1) / (1 + (17549061 / 2000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((59049 / 102400000 : ℝ) * ((199167779 / 156250000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-747124985277403 / 1000000000000000000 : ℝ)
  interval_num

theorem cell3_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (2917047569 / 10000000000 : ℝ) (17549061 / 2000000000 : ℝ) (199167779 / 156250000 : ℝ)) ≤ (634106115283191 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (455418818260910189 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell3_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-3563468499 / 5000000000 : ℝ) (6906919 / 5000000000 : ℝ) (156677523 / 250000000 : ℝ) ≤ (-689493026582917 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-3563468499 / 5000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (283312267090103 / 390625000000000 : ℝ) ≤ e ∧ e ≤ (362639701876331841 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (6906919 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-38112351419549603 / 62500000000000000 : ℝ) ≤ k ∧ k ≤ (-304898811354176277 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (6906919 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-379566608476717 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-11861456452311 / 31250000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (59049 / 102400000 : ℝ) / ((156677523 / 250000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (97974812649811419 / 250000000000000000 : ℝ) ≤ ea ∧ ea ≤ (24493703163069401 / 62500000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2208048931611397 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-441609785915107 / 200000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-3563468499 / 5000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (6906919 / 5000000000 : ℝ) * (e - 1) / (1 + (6906919 / 5000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(59049 / 102400000 : ℝ) * ((156677523 / 250000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-689493026582917 / 1000000000000000000 : ℝ)
  interval_num

theorem cell3_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-3563468499 / 5000000000 : ℝ) (6906919 / 5000000000 : ℝ) (156677523 / 250000000 : ℝ)) ≤ (2011063900616839 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (229355749531919411 / 250000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell3_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2917047569 / 10000000000 : ℝ)
  τm := (-3563468499 / 5000000000 : ℝ)
  vp := (17549061 / 2000000000 : ℝ)
  vm := (6906919 / 5000000000 : ℝ)
  bp := (199167779 / 156250000 : ℝ)
  bm := (156677523 / 250000000 : ℝ)
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
  plus_nonpos := cell3_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell3_0_minus_exponent.trans (by norm_num)

theorem cell3_0_payment : cell3_0.payment ≤ endpointIntercept + radiusPrice * (19683 / 51200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell3_0_plus_tail cell3_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell4_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (144621467 / 500000000 : ℝ) (88035299 / 10000000000 : ℝ) (6364218417 / 5000000000 : ℝ) ≤ (-730382933620993 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((144621467 / 500000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (284808646542415129 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (1139234586171660517 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (88035299 / 10000000000 : ℝ) * (e - 1)))
  have hk : (308563660690044381 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (19285228793405131 / 62500000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (88035299 / 10000000000 : ℝ) * (e - 1))
  have hlw : (612502608046199 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1225005218110007 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (177147 / 204800000 : ℝ) / ((6364218417 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (812768454088089187 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (406384227047384103 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3331130036952921 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (1665565019512089 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (144621467 / 500000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (88035299 / 10000000000 : ℝ) * (e - 1) / (1 + (88035299 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((177147 / 204800000 : ℝ) * ((6364218417 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-730382933620993 / 1000000000000000000 : ℝ)
  interval_num

theorem cell4_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (144621467 / 500000000 : ℝ) (88035299 / 10000000000 : ℝ) (6364218417 / 5000000000 : ℝ)) ≤ (176998603057 / 61035156250000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (114093224228101827 / 125000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell4_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-7084120547 / 10000000000 : ℝ) (3441621 / 2500000000 : ℝ) (63043889 / 100000000 : ℝ) ≤ (-338230789357473 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-7084120547 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (29067211930784961 / 40000000000000000 : ℝ) ≤ e ∧ e ≤ (726680298271624027 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (3441621 / 2500000000 : ℝ) * (e - 1)))
  have hk : (-606686095534755597 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-606686095530314531 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3441621 / 2500000000 : ℝ) * (e - 1))
  have hlw : (-376335936561303 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-376335934558547 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (177147 / 204800000 : ℝ) / ((63043889 / 100000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (396583318553050219 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (396583318562827791 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-2191022164176237 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-2191022162140693 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-7084120547 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3441621 / 2500000000 : ℝ) * (e - 1) / (1 + (3441621 / 2500000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(177147 / 204800000 : ℝ) * ((63043889 / 100000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-338230789357473 / 500000000000000000 : ℝ)
  interval_num

theorem cell4_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-7084120547 / 10000000000 : ℝ) (3441621 / 2500000000 : ℝ) (63043889 / 100000000 : ℝ)) ≤ (4464077782543963 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (459459317343976349 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell4_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (144621467 / 500000000 : ℝ)
  τm := (-7084120547 / 10000000000 : ℝ)
  vp := (88035299 / 10000000000 : ℝ)
  vm := (3441621 / 2500000000 : ℝ)
  bp := (6364218417 / 5000000000 : ℝ)
  bm := (63043889 / 100000000 : ℝ)
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
  plus_nonpos := cell4_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell4_0_minus_exponent.trans (by norm_num)

theorem cell4_0_payment : cell4_0.payment ≤ endpointIntercept + radiusPrice * (59049 / 102400000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell4_0_plus_tail cell4_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell5_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (2758969107 / 10000000000 : ℝ) (88480771 / 10000000000 : ℝ) (6306429057 / 5000000000 : ℝ) ≤ (-669403431553167 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2758969107 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (11324028681649723 / 10000000000000000 : ℝ) ≤ e ∧ e ≤ (1132402868166972301 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (88480771 / 10000000000 : ℝ) * (e - 1)))
  have hk : (146719749682362491 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (146719749684581349 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (88480771 / 10000000000 : ℝ) * (e - 1))
  have hlw : (46833004059821 / 40000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1170825103513223 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (1594323 / 819200000 : ℝ) / ((6306429057 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (49871829132589469 / 31250000000000000 : ℝ) ≤ ea ∧ ea ≤ (797949266128072287 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (3173548938776603 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (3173548940847451 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2758969107 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (88480771 / 10000000000 : ℝ) * (e - 1) / (1 + (88480771 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((1594323 / 819200000 : ℝ) * ((6306429057 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-669403431553167 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (2758969107 / 10000000000 : ℝ) (88480771 / 10000000000 : ℝ) (6306429057 / 5000000000 : ℝ)) ≤ (4723395027988691 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (459864862652156777 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell5_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-1725169703 / 2500000000 : ℝ) (3403739 / 2500000000 : ℝ) (6449919217 / 10000000000 : ℝ) ≤ (-628461952957693 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1725169703 / 2500000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (732712951338576847 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (45794559458786053 / 62500000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (3403739 / 2500000000 : ℝ) * (e - 1)))
  have hk : (-29664405951449927 / 50000000000000000 : ℝ) ≤ k ∧ k ≤ (-118657623804911517 / 200000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3403739 / 2500000000 : ℝ) * (e - 1))
  have hlw : (-363976373053427 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-363976371050701 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (1594323 / 819200000 : ℝ) / ((6449919217 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (207566034049005993 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (415132068107473899 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-424719918415791 / 200000000000000000 : ℝ) ≤ la ∧ la ≤ (-2123599590044561 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1725169703 / 2500000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3403739 / 2500000000 : ℝ) * (e - 1) / (1 + (3403739 / 2500000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(1594323 / 819200000 : ℝ) * ((6449919217 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-628461952957693 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-1725169703 / 2500000000 : ℝ) (3403739 / 2500000000 : ℝ) (6449919217 / 10000000000 : ℝ)) ≤ (6553895825739839 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (92444867691622329 / 100000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell5_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2758969107 / 10000000000 : ℝ)
  τm := (-1725169703 / 2500000000 : ℝ)
  vp := (88480771 / 10000000000 : ℝ)
  vm := (3403739 / 2500000000 : ℝ)
  bp := (6306429057 / 5000000000 : ℝ)
  bm := (6449919217 / 10000000000 : ℝ)
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
  plus_nonpos := cell5_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell5_0_minus_exponent.trans (by norm_num)

theorem cell5_0_payment : cell5_0.payment ≤ endpointIntercept + radiusPrice * (177147 / 204800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell5_0_plus_tail cell5_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell6_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (1237244041 / 5000000000 : ℝ) (17936301 / 2000000000 : ℝ) (12366860729 / 10000000000 : ℝ) ≤ (-271179787544539 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1237244041 / 5000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (111797694812979163 / 100000000000000000 : ℝ) ≤ e ∧ e ≤ (1117976948131791631 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (17936301 / 2000000000 : ℝ) * (e - 1)))
  have hk : (26149751400324237 / 100000000000000000 : ℝ) ≤ k ∧ k ≤ (261497514007680087 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (17936301 / 2000000000 : ℝ) * (e - 1))
  have hlw : (132184462598589 / 125000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1057475702806651 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (14348907 / 3276800000 : ℝ) / ((12366860729 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1533746722832406901 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1533746722845539561 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (1421510000738537 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (2843020003547127 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1237244041 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (17936301 / 2000000000 : ℝ) * (e - 1) / (1 + (17936301 / 2000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((14348907 / 3276800000 : ℝ) * ((12366860729 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-271179787544539 / 500000000000000000 : ℝ)
  interval_num

theorem cell6_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (1237244041 / 5000000000 : ℝ) (17936301 / 2000000000 : ℝ) (12366860729 / 10000000000 : ℝ)) ≤ (3262795415031253 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (934452066240146413 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell6_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-6408297983 / 10000000000 : ℝ) (6671039 / 5000000000 : ℝ) (6792153011 / 10000000000 : ℝ) ≤ (-32858502269311 / 62500000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6408297983 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (749154128372688687 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (749154128374688689 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (6671039 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-69597238515311473 / 125000000000000000 : ℝ) ≤ k ∧ k ≤ (-556777908118051087 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (6671039 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-334736537546807 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-334736535544137 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (14348907 / 3276800000 : ℝ) / ((6792153011 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (230215287179070049 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (460430574366965119 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-9794819167403 / 5000000000000000 : ℝ) ≤ la ∧ la ≤ (-1958963831448527 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6408297983 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (6671039 / 5000000000 : ℝ) * (e - 1) / (1 + (6671039 / 5000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(14348907 / 3276800000 : ℝ) * ((6792153011 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-32858502269311 / 62500000000000000 : ℝ)
  interval_num

theorem cell6_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-6408297983 / 10000000000 : ℝ) (6671039 / 5000000000 : ℝ) (6792153011 / 10000000000 : ℝ)) ≤ (2981507592588899 / 200000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (936395822567695591 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell6_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1237244041 / 5000000000 : ℝ)
  τm := (-6408297983 / 10000000000 : ℝ)
  vp := (17936301 / 2000000000 : ℝ)
  vm := (6671039 / 5000000000 : ℝ)
  bp := (12366860729 / 10000000000 : ℝ)
  bm := (6792153011 / 10000000000 : ℝ)
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
  plus_nonpos := cell6_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell6_0_minus_exponent.trans (by norm_num)

theorem cell6_0_payment : cell6_0.payment ≤ endpointIntercept + radiusPrice * (1594323 / 819200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell6_0_plus_tail cell6_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell7_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (2216222461 / 10000000000 : ℝ) (45336791 / 5000000000 : ℝ) (12138598727 / 10000000000 : ℝ) ≤ (-109985191829673 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2216222461 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (138129951968734843 / 125000000000000000 : ℝ) ≤ e ∧ e ≤ (221007923150375749 / 200000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (45336791 / 5000000000 : ℝ) * (e - 1)))
  have hk : (58211575931336941 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (116423151864892741 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (45336791 / 5000000000 : ℝ) * (e - 1))
  have hlw : (59498659049621 / 62500000000000000 : ℝ) ≤ lw ∧ lw ≤ (118997318351509 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (43046721 / 6553600000 : ℝ) / ((12138598727 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (738603216165574357 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (5770337626344269 / 3906250000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2542238700277003 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (317779837793283 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2216222461 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (45336791 / 5000000000 : ℝ) * (e - 1) / (1 + (45336791 / 5000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((43046721 / 6553600000 : ℝ) * ((12138598727 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-109985191829673 / 250000000000000000 : ℝ)
  interval_num

theorem cell7_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (2216222461 / 10000000000 : ℝ) (45336791 / 5000000000 : ℝ) (12138598727 / 10000000000 : ℝ)) ≤ (14806732262449359 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (946492155837068753 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell7_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-148677113 / 250000000 : ℝ) (13065709 / 10000000000 : ℝ) (886569533 / 1250000000 : ℝ) ≤ (-219944018738011 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-148677113 / 250000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (382444531549893421 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (191222265775446711 / 250000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (13065709 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-260919135159804487 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-521838270315168521 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (13065709 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-153618150832299 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-307236299661983 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (43046721 / 6553600000 : ℝ) / ((886569533 / 1250000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (4017081254850429 / 8000000000000000 : ℝ) ≤ ea ∧ ea ≤ (502135156864640309 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-903707009851151 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (-1807414017672007 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-148677113 / 250000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (13065709 / 10000000000 : ℝ) * (e - 1) / (1 + (13065709 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(43046721 / 6553600000 : ℝ) * ((886569533 / 1250000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-219944018738011 / 500000000000000000 : ℝ)
  interval_num

theorem cell7_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-148677113 / 250000000 : ℝ) (13065709 / 10000000000 : ℝ) (886569533 / 1250000000 : ℝ)) ≤ (2962595926669899 / 100000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (473249197202718427 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell7_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2216222461 / 10000000000 : ℝ)
  τm := (-148677113 / 250000000 : ℝ)
  vp := (45336791 / 5000000000 : ℝ)
  vm := (13065709 / 10000000000 : ℝ)
  bp := (12138598727 / 10000000000 : ℝ)
  bm := (886569533 / 1250000000 : ℝ)
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
  plus_nonpos := cell7_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell7_0_minus_exponent.trans (by norm_num)

theorem cell7_0_payment : cell7_0.payment ≤ endpointIntercept + radiusPrice * (14348907 / 3276800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell7_0_plus_tail cell7_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell8_0_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (1752055127 / 10000000000 : ℝ) (23100891 / 2500000000 : ℝ) (5859286649 / 5000000000 : ℝ) ≤ (-56491881245489 / 200000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1752055127 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (216432638401759321 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (541081596005398303 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (23100891 / 2500000000 : ℝ) * (e - 1)))
  have hk : (45542553365250587 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (182170213465440067 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (23100891 / 2500000000 : ℝ) * (e - 1))
  have hlw : (379464558276257 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (758929118570997 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (105401599641 / 10000000000000 : ℝ) / ((5859286649 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1376003855267318709 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (13760038552800177 / 10000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (500909586190797 / 250000000000000000 : ℝ) ≤ la ∧ la ≤ (125227396676933 / 62500000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1752055127 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (23100891 / 2500000000 : ℝ) * (e - 1) / (1 + (23100891 / 2500000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * ((105401599641 / 10000000000000 : ℝ) * ((5859286649 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-56491881245489 / 200000000000000000 : ℝ)
  interval_num

theorem cell8_0_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (1752055127 / 10000000000 : ℝ) (23100891 / 2500000000 : ℝ) (5859286649 / 5000000000 : ℝ)) ≤ (52192189051787697 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_0_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (482654304943559587 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell8_0_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-5045430263 / 10000000000 : ℝ) (12537433 / 10000000000 : ℝ) (3814727189 / 5000000000 : ℝ) ≤ (-301376846313369 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-5045430263 / 10000000000 : ℝ) * (922997 / 2048000 : ℝ))
  have he : (398305609304631981 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (796611218611263963 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((922997 / 2048000 : ℝ) * (1 + (12537433 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-28212880704228903 / 62500000000000000 : ℝ) ≤ k ∧ k ≤ (-225703045631611231 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (12537433 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-255029840308913 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-255029838306403 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (105401599641 / 10000000000000 : ℝ) / ((3814727189 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (290600775395314027 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (290600775399115721 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-23752477677253 / 15625000000000000 : ℝ) ≤ la ∧ la ≤ (-152015856931657 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-5045430263 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (12537433 / 10000000000 : ℝ) * (e - 1) / (1 + (12537433 / 10000000000 : ℝ) * (e - 1))) / (922997 / 2048000 : ℝ) + k * (-(105401599641 / 10000000000000 : ℝ) * ((3814727189 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-301376846313369 / 1000000000000000000 : ℝ)
  interval_num

theorem cell8_0_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (922997 / 2048000 : ℝ) agentFrame (-5045430263 / 10000000000 : ℝ) (12537433 / 10000000000 : ℝ) (3814727189 / 5000000000 : ℝ)) ≤ (89724198894629049 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_0_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (963028660650719619 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell8_0 : EndCertificate 8000 (922997 / 2048000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1752055127 / 10000000000 : ℝ)
  τm := (-5045430263 / 10000000000 : ℝ)
  vp := (23100891 / 2500000000 : ℝ)
  vm := (12537433 / 10000000000 : ℝ)
  bp := (5859286649 / 5000000000 : ℝ)
  bm := (3814727189 / 5000000000 : ℝ)
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
  plus_nonpos := cell8_0_plus_exponent.trans (by norm_num)
  minus_nonpos := cell8_0_minus_exponent.trans (by norm_num)

theorem cell8_0_payment : cell8_0.payment ≤ endpointIntercept + radiusPrice * (43046721 / 6553600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (0 / 1 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell8_0_plus_tail cell8_0_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

end BstLean.Part293.Coarse
