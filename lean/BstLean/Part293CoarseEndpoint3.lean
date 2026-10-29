import BstLean.Part293EndpointInterface
import BstLean.Part293ScalarTools

namespace BstLean.Part293.Coarse
open Real BstLean.Part156 BstLean.Part203 BstLean.Part232 BstLean.Part236

theorem cell0_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1278937821 / 5000000000 : ℝ) (16570809 / 2000000000 : ℝ) (6219848329 / 5000000000 : ℝ) ≤ (-666740974571269 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1278937821 / 5000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (1209441726298837101 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (604720863150418551 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (16570809 / 2000000000 : ℝ) * (e - 1)))
  have hk : (140618697042059451 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (281237394086809149 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (16570809 / 2000000000 : ℝ) * (e - 1))
  have hlw : (1733805510751069 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (866902756383821 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (2187 / 12800000 : ℝ) / ((6219848329 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1552017059858193771 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (388004264966679877 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2940194642142811 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (294019464418829 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1278937821 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (16570809 / 2000000000 : ℝ) * (e - 1) / (1 + (16570809 / 2000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((2187 / 12800000 : ℝ) * ((6219848329 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-666740974571269 / 1000000000000000000 : ℝ)
  interval_num

theorem cell0_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1278937821 / 5000000000 : ℝ) (16570809 / 2000000000 : ℝ) (6219848329 / 5000000000 : ℝ)) ≤ (1206270202070953 / 250000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (920035868848437983 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell0_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-3250176677 / 5000000000 : ℝ) (3234373 / 2000000000 : ℝ) (3352852651 / 5000000000 : ℝ) ≤ (-629082827723969 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-3250176677 / 5000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (24670962256112651 / 40000000000000000 : ℝ) ≤ e ∧ e ≤ (616774056404816277 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (3234373 / 2000000000 : ℝ) * (e - 1)))
  have hk : (-257903348908598471 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-128951674453625837 / 250000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3234373 / 2000000000 : ℝ) * (e - 1))
  have hlw : (-309969973249751 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-77492493062033 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (2187 / 12800000 : ℝ) / ((3352852651 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (448765796325218177 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (448765796331864729 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-400271290003851 / 200000000000000000 : ℝ) ≤ la ∧ la ≤ (-2001356447995097 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-3250176677 / 5000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3234373 / 2000000000 : ℝ) * (e - 1) / (1 + (3234373 / 2000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(2187 / 12800000 : ℝ) * ((3352852651 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (2187 / 12800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-629082827723969 / 1000000000000000000 : ℝ)
  interval_num

theorem cell0_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-3250176677 / 5000000000 : ℝ) (3234373 / 2000000000 : ℝ) (3352852651 / 5000000000 : ℝ)) ≤ (3260711674776483 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell0_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (231094233460799761 / 250000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell0_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (2187 / 12800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1278937821 / 5000000000 : ℝ)
  τm := (-3250176677 / 5000000000 : ℝ)
  vp := (16570809 / 2000000000 : ℝ)
  vm := (3234373 / 2000000000 : ℝ)
  bp := (6219848329 / 5000000000 : ℝ)
  bm := (3352852651 / 5000000000 : ℝ)
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
  plus_nonpos := cell0_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell0_3_minus_exponent.trans (by norm_num)

theorem cell0_3_payment : cell0_3.payment ≤ endpointIntercept + radiusPrice * (0 / 1 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell0_3_plus_tail cell0_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell1_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (79599127 / 312500000 : ℝ) (41439031 / 5000000000 : ℝ) (2485961157 / 2000000000 : ℝ) ≤ (-662377713156047 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((79599127 / 312500000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (241695943826011163 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (151059964891506977 / 125000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (41439031 / 5000000000 : ℝ) * (e - 1)))
  have hk : (279947702811287281 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (34993462851747191 / 125000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (41439031 / 5000000000 : ℝ) * (e - 1))
  have hlw : (53948390947461 / 31250000000000000 : ℝ) ≤ lw ∧ lw ≤ (1726348512335329 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (6561 / 25600000 : ℝ) / ((2485961157 / 2000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (774764752669408417 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (4728788773643 / 3051757812500 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (731741153527579 / 250000000000000000 : ℝ) ≤ la ∧ la ≤ (2926964616155773 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (79599127 / 312500000 : ℝ) * (1 / 100 : ℝ) + ((lw - (41439031 / 5000000000 : ℝ) * (e - 1) / (1 + (41439031 / 5000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((6561 / 25600000 : ℝ) * ((2485961157 / 2000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-662377713156047 / 1000000000000000000 : ℝ)
  interval_num

theorem cell1_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (79599127 / 312500000 : ℝ) (41439031 / 5000000000 : ℝ) (2485961157 / 2000000000 : ℝ)) ≤ (624559943348383 / 125000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (460268900170267679 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell1_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-6466100193 / 10000000000 : ℝ) (8091939 / 5000000000 : ℝ) (3361184933 / 5000000000 : ℝ) ≤ (-625546374019441 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6466100193 / 10000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (123669330352798427 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (618346651765992137 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (8091939 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-51368897619602359 / 100000000000000000 : ℝ) ≤ k ∧ k ≤ (-256844488096665003 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (8091939 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-77231744508123 / 125000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-617853954061743 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (6561 / 25600000 : ℝ) / ((3361184933 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (451002718968056923 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (112750679743671943 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1993226794389389 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-249153349045661 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6466100193 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (8091939 / 5000000000 : ℝ) * (e - 1) / (1 + (8091939 / 5000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(6561 / 25600000 : ℝ) * ((3361184933 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (6561 / 25600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-625546374019441 / 1000000000000000000 : ℝ)
  interval_num

theorem cell1_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-6466100193 / 10000000000 : ℝ) (8091939 / 5000000000 : ℝ) (3361184933 / 5000000000 : ℝ)) ≤ (6708559758560611 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell1_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (57799103200229879 / 62500000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell1_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (6561 / 25600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (79599127 / 312500000 : ℝ)
  τm := (-6466100193 / 10000000000 : ℝ)
  vp := (41439031 / 5000000000 : ℝ)
  vm := (8091939 / 5000000000 : ℝ)
  bp := (2485961157 / 2000000000 : ℝ)
  bm := (3361184933 / 5000000000 : ℝ)
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
  plus_nonpos := cell1_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell1_3_minus_exponent.trans (by norm_num)

theorem cell1_3_payment : cell1_3.payment ≤ endpointIntercept + radiusPrice * (2187 / 12800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell1_3_plus_tail cell1_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell2_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1269304601 / 5000000000 : ℝ) (16605917 / 2000000000 : ℝ) (12423649531 / 10000000000 : ℝ) ≤ (-327929391436539 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1269304601 / 5000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (603855332199994817 / 500000000000000000 : ℝ) ≤ e ∧ e ≤ (241542132880397927 / 200000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (16605917 / 2000000000 : ℝ) * (e - 1)))
  have hk : (139457955147169049 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (34864488787128543 / 125000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (16605917 / 2000000000 : ℝ) * (e - 1))
  have hlw : (215390948512437 / 125000000000000000 : ℝ) ≤ lw ∧ lw ≤ (215390948764513 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (19683 / 51200000 : ℝ) / ((12423649531 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1547982239916289687 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (386995559981203441 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2918735413747199 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (291873541579267 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1269304601 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (16605917 / 2000000000 : ℝ) * (e - 1) / (1 + (16605917 / 2000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((19683 / 51200000 : ℝ) * ((12423649531 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-327929391436539 / 500000000000000000 : ℝ)
  interval_num

theorem cell2_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1269304601 / 5000000000 : ℝ) (16605917 / 2000000000 : ℝ) (12423649531 / 10000000000 : ℝ)) ≤ (328997967458743 / 62500000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (460644110631636449 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell2_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1293648203 / 2000000000 : ℝ) (3223733 / 2000000000 : ℝ) (1346035139 / 2000000000 : ℝ) ≤ (-620254588664983 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1293648203 / 2000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (618248247215113293 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (123649649443422659 / 200000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (3223733 / 2000000000 : ℝ) * (e - 1)))
  have hk : (-256910113203587177 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-32113764150280049 / 62500000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (3223733 / 2000000000 : ℝ) * (e - 1))
  have hlw : (-615522257593491 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-615522255590263 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (19683 / 51200000 : ℝ) / ((1346035139 / 2000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (9041048706313331 / 20000000000000000 : ℝ) ≤ ea ∧ ea ≤ (56506554415284993 / 125000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1989411829452671 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-1989411827428633 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1293648203 / 2000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (3223733 / 2000000000 : ℝ) * (e - 1) / (1 + (3223733 / 2000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(19683 / 51200000 : ℝ) * ((1346035139 / 2000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (19683 / 51200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-620254588664983 / 1000000000000000000 : ℝ)
  interval_num

theorem cell2_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1293648203 / 2000000000 : ℝ) (3223733 / 2000000000 : ℝ) (1346035139 / 2000000000 : ℝ)) ≤ (6998659073183863 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell2_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (115674696807800693 / 125000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell2_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (19683 / 51200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1269304601 / 5000000000 : ℝ)
  τm := (-1293648203 / 2000000000 : ℝ)
  vp := (16605917 / 2000000000 : ℝ)
  vm := (3223733 / 2000000000 : ℝ)
  bp := (12423649531 / 10000000000 : ℝ)
  bm := (1346035139 / 2000000000 : ℝ)
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
  plus_nonpos := cell2_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell2_3_minus_exponent.trans (by norm_num)

theorem cell2_3_payment : cell2_3.payment ≤ endpointIntercept + radiusPrice * (6561 / 25600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell2_3_plus_tail cell2_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell3_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (29737 / 40000 : ℝ) agentFrame (314315769 / 1250000000 : ℝ) (2596353 / 312500000 : ℝ) (12401365861 / 10000000000 : ℝ) ≤ (-161537208597771 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((314315769 / 1250000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (301387580202096773 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (1205550320810387093 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (2596353 / 312500000 : ℝ) * (e - 1)))
  have hk : (17251226131377929 / 62500000000000000 : ℝ) ≤ k ∧ k ≤ (276019618104737111 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (2596353 / 312500000 : ℝ) * (e - 1))
  have hlw : (426580803960973 / 250000000000000000 : ℝ) ≤ lw ∧ lw ≤ (1706323217860511 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (59049 / 102400000 : ℝ) / ((12401365861 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (308477651036675581 / 200000000000000000 : ℝ) ≤ ea ∧ ea ≤ (385597063797973049 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2888982990694711 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (288898299274013 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (314315769 / 1250000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (2596353 / 312500000 : ℝ) * (e - 1) / (1 + (2596353 / 312500000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((59049 / 102400000 : ℝ) * ((12401365861 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-161537208597771 / 250000000000000000 : ℝ)
  interval_num

theorem cell3_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (29737 / 40000 : ℝ) agentFrame (314315769 / 1250000000 : ℝ) (2596353 / 312500000 : ℝ) (12401365861 / 10000000000 : ℝ)) ≤ (5689171344760313 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (184481421558452717 / 200000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell3_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-6408297983 / 10000000000 : ℝ) (8059241 / 5000000000 : ℝ) (270482179 / 400000000 : ℝ) ≤ (-38272290373231 / 62500000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-6408297983 / 10000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (124201900801882249 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (38813094000713203 / 62500000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (8059241 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-510101427016787481 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-255050713507046967 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (8059241 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-611061810024511 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-152765452005321 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (59049 / 102400000 : ℝ) / ((270482179 / 400000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (228176088201428823 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (456352176409438249 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1973785510903499 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-1973785508879581 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-6408297983 / 10000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (8059241 / 5000000000 : ℝ) * (e - 1) / (1 + (8059241 / 5000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(59049 / 102400000 : ℝ) * ((270482179 / 400000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (59049 / 102400000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-38272290373231 / 62500000000000000 : ℝ)
  interval_num

theorem cell3_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-6408297983 / 10000000000 : ℝ) (8059241 / 5000000000 : ℝ) (270482179 / 400000000 : ℝ)) ≤ (1491025590343493 / 200000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell3_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (231577904426484743 / 250000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell3_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (59049 / 102400000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (314315769 / 1250000000 : ℝ)
  τm := (-6408297983 / 10000000000 : ℝ)
  vp := (2596353 / 312500000 : ℝ)
  vm := (8059241 / 5000000000 : ℝ)
  bp := (12401365861 / 10000000000 : ℝ)
  bm := (270482179 / 400000000 : ℝ)
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
  plus_nonpos := cell3_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell3_3_minus_exponent.trans (by norm_num)

theorem cell3_3_payment : cell3_3.payment ≤ endpointIntercept + radiusPrice * (19683 / 51200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell3_3_plus_tail cell3_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell4_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (2478133989 / 10000000000 : ℝ) (83159541 / 10000000000 : ℝ) (618380671 / 500000000 : ℝ) ≤ (-631716735755379 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((2478133989 / 10000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (12022931313731079 / 10000000000000000 : ℝ) ≤ e ∧ e ≤ (1202293131375107901 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (83159541 / 10000000000 : ℝ) * (e - 1)))
  have hk : (271652679393450471 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (135826339698070359 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (83159541 / 10000000000 : ℝ) * (e - 1))
  have hlw : (168084697915811 / 100000000000000000 : ℝ) ≤ lw ∧ lw ≤ (210105872646843 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (177147 / 204800000 : ℝ) / ((618380671 / 500000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (11983866898590089 / 7812500000000000 : ℝ) ≤ ea ∧ ea ≤ (1533934963028030643 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (28440212447577 / 10000000000000000 : ℝ) ≤ la ∧ la ≤ (1422010623401519 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (2478133989 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (83159541 / 10000000000 : ℝ) * (e - 1) / (1 + (83159541 / 10000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((177147 / 204800000 : ℝ) * ((618380671 / 500000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-631716735755379 / 1000000000000000000 : ℝ)
  interval_num

theorem cell4_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (2478133989 / 10000000000 : ℝ) (83159541 / 10000000000 : ℝ) (618380671 / 500000000 : ℝ)) ≤ (6385446349600377 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (231018160864810249 / 250000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell4_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1590433773 / 2500000000 : ℝ) (16050357 / 10000000000 : ℝ) (1698956649 / 2500000000 : ℝ) ≤ (-600587552640079 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1590433773 / 2500000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (155790729139301761 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (311581458279603523 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (16050357 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-253599990842507521 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (-507199981682321529 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (16050357 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-18906873771243 / 31250000000000000 : ℝ) ≤ lw ∧ lw ≤ (-605019958676563 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (177147 / 204800000 : ℝ) / ((1698956649 / 2500000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (460929599371380997 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (46092959937791781 / 100000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-244643787039857 / 125000000000000000 : ℝ) ≤ la ∧ la ≤ (-1957150294295097 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1590433773 / 2500000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (16050357 / 10000000000 : ℝ) * (e - 1) / (1 + (16050357 / 10000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(177147 / 204800000 : ℝ) * ((1698956649 / 2500000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (177147 / 204800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-600587552640079 / 1000000000000000000 : ℝ)
  interval_num

theorem cell4_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1590433773 / 2500000000 : ℝ) (16050357 / 10000000000 : ℝ) (1698956649 / 2500000000 : ℝ)) ≤ (8191154544306991 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell4_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (463837675782396261 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell4_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (177147 / 204800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (2478133989 / 10000000000 : ℝ)
  τm := (-1590433773 / 2500000000 : ℝ)
  vp := (83159541 / 10000000000 : ℝ)
  vm := (16050357 / 10000000000 : ℝ)
  bp := (618380671 / 500000000 : ℝ)
  bm := (1698956649 / 2500000000 : ℝ)
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
  plus_nonpos := cell4_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell4_3_minus_exponent.trans (by norm_num)

theorem cell4_3_payment : cell4_3.payment ≤ endpointIntercept + radiusPrice * (59049 / 102400000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell4_3_plus_tail cell4_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell5_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1186669637 / 5000000000 : ℝ) (20982037 / 2500000000 : ℝ) (3069285229 / 2500000000 : ℝ) ≤ (-579146955846447 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1186669637 / 5000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (1192962816989313771 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (1192962816991313773 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (20982037 / 2500000000 : ℝ) * (e - 1)))
  have hk : (259139548387250499 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (64784887097485187 / 250000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (20982037 / 2500000000 : ℝ) * (e - 1))
  have hlw : (323638241476241 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (202273901174749 / 125000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (1594323 / 819200000 : ℝ) / ((3069285229 / 2500000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (1511393500387728137 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (94462093774763051 / 62500000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (2724116828183267 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (1362058415114253 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1186669637 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (20982037 / 2500000000 : ℝ) * (e - 1) / (1 + (20982037 / 2500000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((1594323 / 819200000 : ℝ) * ((3069285229 / 2500000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-579146955846447 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1186669637 / 5000000000 : ℝ) (20982037 / 2500000000 : ℝ) (3069285229 / 2500000000 : ℝ)) ≤ (9723830568803161 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (465082462671186341 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell5_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-617561733 / 1000000000 : ℝ) (987889 / 625000000 : ℝ) (6924571183 / 10000000000 : ℝ) ≤ (-557314112506163 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-617561733 / 1000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (631845212756277087 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (631845212758277089 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (987889 / 625000000 : ℝ) * (e - 1)))
  have hk : (-15484461541928311 / 31250000000000000 : ℝ) ≤ k ∧ k ≤ (-247751384669506281 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (987889 / 625000000 : ℝ) * (e - 1))
  have hlw : (-291041540937833 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-291041539936251 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (1594323 / 819200000 : ℝ) / ((6924571183 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (478590045397623891 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (119647511351000503 / 250000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-946485756318511 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (-946485755306921 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-617561733 / 1000000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (987889 / 625000000 : ℝ) * (e - 1) / (1 + (987889 / 625000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(1594323 / 819200000 : ℝ) * ((6924571183 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (1594323 / 819200000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-557314112506163 / 1000000000000000000 : ℝ)
  interval_num

theorem cell5_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-617561733 / 1000000000 : ℝ) (987889 / 625000000 : ℝ) (6924571183 / 10000000000 : ℝ)) ≤ (5789785234682907 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell5_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (932706910574428601 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell5_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (1594323 / 819200000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1186669637 / 5000000000 : ℝ)
  τm := (-617561733 / 1000000000 : ℝ)
  vp := (20982037 / 2500000000 : ℝ)
  vm := (987889 / 625000000 : ℝ)
  bp := (3069285229 / 2500000000 : ℝ)
  bm := (6924571183 / 10000000000 : ℝ)
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
  plus_nonpos := cell5_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell5_3_minus_exponent.trans (by norm_num)

theorem cell5_3_payment : cell5_3.payment ≤ endpointIntercept + radiusPrice * (177147 / 204800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell5_3_plus_tail cell5_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell6_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (531711897 / 2500000000 : ℝ) (42732201 / 5000000000 : ℝ) (12058329193 / 10000000000 : ℝ) ≤ (-469560830801067 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((531711897 / 2500000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (46852043277978153 / 40000000000000000 : ℝ) ≤ e ∧ e ≤ (585650540975726913 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (42732201 / 5000000000 : ℝ) * (e - 1)))
  have hk : (230084623612450669 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (230084623615140917 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (42732201 / 5000000000 : ℝ) * (e - 1))
  have hlw : (1462943827729179 / 1000000000000000000 : ℝ) ≤ lw ∧ lw ≤ (731471914873137 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (14348907 / 3276800000 : ℝ) / ((12058329193 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (728791012244613269 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (291516404899529573 / 200000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (487564044936099 / 200000000000000000 : ℝ) ≤ la ∧ la ≤ (1218910113362709 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (531711897 / 2500000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (42732201 / 5000000000 : ℝ) * (e - 1) / (1 + (42732201 / 5000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((14348907 / 3276800000 : ℝ) * ((12058329193 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-469560830801067 / 1000000000000000000 : ℝ)
  interval_num

theorem cell6_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (531711897 / 2500000000 : ℝ) (42732201 / 5000000000 : ℝ) (12058329193 / 10000000000 : ℝ)) ≤ (11682844130502097 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (942994240644716707 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell6_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-28516659 / 50000000 : ℝ) (7651391 / 5000000000 : ℝ) (1805633111 / 2500000000 : ℝ) ≤ (-465067564880227 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-28516659 / 50000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (163605979583027801 / 250000000000000000 : ℝ) ≤ e ∧ e ≤ (327211959167055603 / 500000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (7651391 / 5000000000 : ℝ) * (e - 1)))
  have hk : (-29068074159544143 / 62500000000000000 : ℝ) ≤ k ∧ k ≤ (-1816754634960989 / 3906250000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (7651391 / 5000000000 : ℝ) * (e - 1))
  have hlw : (-105793484764033 / 200000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-528967421817101 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (14348907 / 3276800000 : ℝ) / ((1805633111 / 2500000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (260371485186941873 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (65092871297491991 / 125000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-869901352232289 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (-869901351221293 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-28516659 / 50000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (7651391 / 5000000000 : ℝ) * (e - 1) / (1 + (7651391 / 5000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(14348907 / 3276800000 : ℝ) * ((1805633111 / 2500000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (14348907 / 3276800000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-465067564880227 / 1000000000000000000 : ℝ)
  interval_num

theorem cell6_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-28516659 / 50000000 : ℝ) (7651391 / 5000000000 : ℝ) (1805633111 / 2500000000 : ℝ)) ≤ (12110436232862539 / 500000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell6_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (943524029896667971 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell6_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (14348907 / 3276800000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (531711897 / 2500000000 : ℝ)
  τm := (-28516659 / 50000000 : ℝ)
  vp := (42732201 / 5000000000 : ℝ)
  vm := (7651391 / 5000000000 : ℝ)
  bp := (12058329193 / 10000000000 : ℝ)
  bm := (1805633111 / 2500000000 : ℝ)
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
  plus_nonpos := cell6_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell6_3_minus_exponent.trans (by norm_num)

theorem cell6_3_payment : cell6_3.payment ≤ endpointIntercept + radiusPrice * (1594323 / 819200000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell6_3_plus_tail cell6_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell7_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (953695399 / 5000000000 : ℝ) (86849001 / 10000000000 : ℝ) (5930334111 / 5000000000 : ℝ) ≤ (-95284507678441 / 250000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((953695399 / 5000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (1152346387186849711 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (72021649199303107 / 62500000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (86849001 / 10000000000 : ℝ) * (e - 1)))
  have hk : (204654244917247 / 1000000000000000 : ℝ) ≤ k ∧ k ≤ (818616979679749 / 4000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (86849001 / 10000000000 : ℝ) * (e - 1))
  have hlw : (661119304716629 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (132223861145063 / 100000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (43046721 / 6553600000 : ℝ) / ((5930334111 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (28196595642404989 / 20000000000000000 : ℝ) ≤ ea ∧ ea ≤ (70491489106430743 / 50000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (1091846142853077 / 500000000000000000 : ℝ) ≤ la ∧ la ≤ (1091846143875389 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (953695399 / 5000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (86849001 / 10000000000 : ℝ) * (e - 1) / (1 + (86849001 / 10000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((43046721 / 6553600000 : ℝ) * ((5930334111 / 5000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-95284507678441 / 250000000000000000 : ℝ)
  interval_num

theorem cell7_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (953695399 / 5000000000 : ℝ) (86849001 / 10000000000 : ℝ) (5930334111 / 5000000000 : ℝ)) ≤ (47401365359511003 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (953474828030949383 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell7_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1322170307 / 2500000000 : ℝ) (739797 / 500000000 : ℝ) (3738803727 / 5000000000 : ℝ) ≤ (-194173236508103 / 500000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1322170307 / 2500000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (674911448451921703 / 1000000000000000000 : ℝ) ≤ e ∧ e ≤ (134982289690784341 / 200000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (739797 / 500000000 : ℝ) * (e - 1)))
  have hk : (-437495368178184819 / 1000000000000000000 : ℝ) ≤ k ∧ k ≤ (-218747684087745987 / 500000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (739797 / 500000000 : ℝ) * (e - 1))
  have hlw : (-240557394250057 / 500000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-3758709269509 / 7812500000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (43046721 / 6553600000 : ℝ) / ((3738803727 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (22330009632368553 / 40000000000000000 : ℝ) ≤ ea ∧ ea ≤ (279125120407504333 / 500000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1603534282412801 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-1603534280391747 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1322170307 / 2500000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (739797 / 500000000 : ℝ) * (e - 1) / (1 + (739797 / 500000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(43046721 / 6553600000 : ℝ) * ((3738803727 / 5000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (43046721 / 6553600000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-194173236508103 / 500000000000000000 : ℝ)
  interval_num

theorem cell7_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1322170307 / 2500000000 : ℝ) (739797 / 500000000 : ℝ) (3738803727 / 5000000000 : ℝ)) ≤ (44745169507126729 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell7_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (238154020360635597 / 250000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell7_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (43046721 / 6553600000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (953695399 / 5000000000 : ℝ)
  τm := (-1322170307 / 2500000000 : ℝ)
  vp := (86849001 / 10000000000 : ℝ)
  vm := (739797 / 500000000 : ℝ)
  bp := (5930334111 / 5000000000 : ℝ)
  bm := (3738803727 / 5000000000 : ℝ)
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
  plus_nonpos := cell7_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell7_3_minus_exponent.trans (by norm_num)

theorem cell7_3_payment : cell7_3.payment ≤ endpointIntercept + radiusPrice * (14348907 / 3276800000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell7_3_plus_tail cell7_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

theorem cell8_3_plus_exponent : endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1511826707 / 10000000000 : ℝ) (17862387 / 2000000000 : ℝ) (11496518097 / 10000000000 : ℝ) ≤ (-245014866913597 / 1000000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((1511826707 / 10000000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (223790499362257107 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (34967265525415173 / 31250000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (17862387 / 2000000000 : ℝ) * (e - 1)))
  have hk : (79918120354617511 / 500000000000000000 : ℝ) ≤ k ∧ k ≤ (159836240711925273 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (17862387 / 2000000000 : ℝ) * (e - 1))
  have hlw : (265455957705691 / 250000000000000000 : ℝ) ≤ lw ∧ lw ≤ (265455958210157 / 250000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 + (105401599641 / 10000000000000 : ℝ) / ((11496518097 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ)))))
  have hea : (661991698320013579 / 500000000000000000 : ℝ) ≤ ea ∧ ea ≤ (1323983396648281153 / 1000000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u + (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (1726672418916079 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (1726672420960109 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (1511826707 / 10000000000 : ℝ) * (1 / 100 : ℝ) + ((lw - (17862387 / 2000000000 : ℝ) * (e - 1) / (1 + (17862387 / 2000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * ((105401599641 / 10000000000000 : ℝ) * ((11496518097 / 10000000000 : ℝ) * (u + (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-245014866913597 / 1000000000000000000 : ℝ)
  interval_num

theorem cell8_3_plus_tail : exp (8000 * endpointPlus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (29737 / 40000 : ℝ) agentFrame (1511826707 / 10000000000 : ℝ) (17862387 / 2000000000 : ℝ) (11496518097 / 10000000000 : ℝ)) ≤ (28168333777355549 / 200000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_3_plus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (969837392278938327 / 1000000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

theorem cell8_3_minus_exponent : endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1116835317 / 2500000000 : ℝ) (13900533 / 10000000000 : ℝ) (7940817013 / 10000000000 : ℝ) ≤ (-53043838736323 / 200000000000000000 : ℝ) := by
  let u : ℝ := √(1 / 100 / aL)
  have hu : (66630010657559783 / 1000000000000000000 : ℝ) ≤ u ∧ u ≤ (8328751332194973 / 125000000000000000 : ℝ) := by
    constructor
    · apply le_sqrt_of_sq_le; norm_num [aL]
    · apply sqrt_le_iff.mpr; constructor <;> norm_num [aL]
  let e : ℝ := exp ((-1116835317 / 2500000000 : ℝ) * (29737 / 40000 : ℝ))
  have he : (143481204615253321 / 200000000000000000 : ℝ) ≤ e ∧ e ≤ (717406023078266607 / 1000000000000000000 : ℝ) := by
    apply exp_enclose (by norm_num)
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  let k : ℝ := (e - 1) / ((29737 / 40000 : ℝ) * (1 + (13900533 / 10000000000 : ℝ) * (e - 1)))
  have hk : (-95068443120847611 / 250000000000000000 : ℝ) ≤ k ∧ k ≤ (-380273772480698073 / 1000000000000000000 : ℝ) := by
    dsimp only [k]
    constructor <;> interval_num
  let lw : ℝ := log (1 + (13900533 / 10000000000 : ℝ) * (e - 1))
  have hlw : (-39289786544137 / 100000000000000000 : ℝ) ≤ lw ∧ lw ≤ (-392897863438587 / 1000000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  let ea : ℝ := exp ((39 / 25 : ℝ) * k * (1 - (105401599641 / 10000000000000 : ℝ) / ((7940817013 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ)))))
  have hea : (629718880298728919 / 1000000000000000000 : ℝ) ≤ ea ∧ ea ≤ (15742972007603033 / 25000000000000000 : ℝ) := by
    apply exp_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [expApprox16]; interval_num
    · dsimp only [expApprox16]; interval_num
  let la : ℝ := log (1 + (u - (1281 / 200000 : ℝ)) ^ 2 * (ea - 1))
  have hla : (-1343931514504221 / 1000000000000000000 : ℝ) ≤ la ∧ la ≤ (-671965756242317 / 500000000000000000 : ℝ) := by
    apply log_one_add_enclose
    · apply abs_le.mpr; constructor <;> interval_num
    · dsimp only [logApprox10]; interval_num
    · dsimp only [logApprox10]; interval_num
  rw [show rootAllowance + samplingDeviation = (1281 / 200000 : ℝ) by norm_num [rootAllowance, samplingDeviation]]
  rw [show agentFrame = (39 / 25 : ℝ) by norm_num [agentFrame]]
  change - (-1116835317 / 2500000000 : ℝ) * (1 / 1000 : ℝ) + ((lw - (13900533 / 10000000000 : ℝ) * (e - 1) / (1 + (13900533 / 10000000000 : ℝ) * (e - 1))) / (29737 / 40000 : ℝ) + k * (-(105401599641 / 10000000000000 : ℝ) * ((7940817013 / 10000000000 : ℝ) * (u - (1281 / 200000 : ℝ))) + (105401599641 / 10000000000000 : ℝ) ^ 2) + la / (39 / 25 : ℝ)) ≤ (-53043838736323 / 200000000000000000 : ℝ)
  interval_num

theorem cell8_3_minus_tail : exp (8000 * endpointMinus .exact aL (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) (29737 / 40000 : ℝ) agentFrame (-1116835317 / 2500000000 : ℝ) (13900533 / 10000000000 : ℝ) (7940817013 / 10000000000 : ℝ)) ≤ (119821331559821097 / 1000000000000000000 : ℝ) := by
  apply (exp_le_exp.mpr (mul_le_mul_of_nonneg_left cell8_3_minus_exponent (by norm_num : (0 : ℝ) ≤ 8000))).trans
  apply exp_scaled_upper (v := (483695559356466379 / 500000000000000000 : ℝ))
  · apply (exp_enclose (by norm_num) (l := -1) _ _).2
    · norm_num [expApprox16]
    · norm_num [expApprox16]
  · norm_num

noncomputable def cell8_3 : EndCertificate 8000 (29737 / 40000 : ℝ) agentFrame aL
    (rootAllowance + samplingDeviation) (105401599641 / 10000000000000 : ℝ) where
  plus := .exact
  minus := .exact
  plus_valid := trivial
  minus_valid := trivial
  τp := (1511826707 / 10000000000 : ℝ)
  τm := (-1116835317 / 2500000000 : ℝ)
  vp := (17862387 / 2000000000 : ℝ)
  vm := (13900533 / 10000000000 : ℝ)
  bp := (11496518097 / 10000000000 : ℝ)
  bm := (7940817013 / 10000000000 : ℝ)
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
  plus_nonpos := cell8_3_plus_exponent.trans (by norm_num)
  minus_nonpos := cell8_3_minus_exponent.trans (by norm_num)

theorem cell8_3_payment : cell8_3.payment ≤ endpointIntercept + radiusPrice * (43046721 / 6553600000 : ℝ) ^ 2 +
    framePrice quadraticPrice linearPrice (2193113 / 10240000 : ℝ) := by
  apply (min_le_right _ _).trans
  apply (add_le_add cell8_3_plus_tail cell8_3_minus_tail).trans
  norm_num [endpointIntercept, radiusPrice, framePrice, quadraticPrice, linearPrice]

end BstLean.Part293.Coarse
