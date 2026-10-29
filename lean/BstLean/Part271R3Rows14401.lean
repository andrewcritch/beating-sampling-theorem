import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14401–14475. -/
namespace BstLean.Part271.R3.Rows14401
open Real BstLean.Part130 BstLean.Part227

theorem width_14401 : mW 14401 = 358405178760263 := by
  have hu : mW 14401 ≤ 358405178760263 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14401 ≤ 358405178760262 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14401 : RowArithmetic 14401 (555893593193547918209/500000000000000000000000) (604886578500196844768163/1000000000000000000000000) (3398258430401151/500000000000000000000000) where
  r0 := (578643427301/1000000000000000000)
  k0 := (359620363719539/100000000000000000)
  k6 := (11410490423984987/1000000000000000000)
  q := (169711519938983517431/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14401]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14401]

theorem width_14402 : mW 14402 = 358492292642101 := by
  have hu : mW 14402 ≤ 358492292642101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14402 ≤ 358492292642100 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14402 : RowArithmetic 14402 (1111758584905746343421/1000000000000000000000000) (604875828852639116081649/1000000000000000000000000) (1698822316217207/250000000000000000000000) where
  r0 := (7232289517/12500000000000000)
  k0 := (899004089826487/250000000000000000)
  k6 := (5705047137271931/500000000000000000)
  q := (169717412188614283031/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14402]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14402]

theorem width_14403 : mW 14403 = 358579421647088 := by
  have hu : mW 14403 ≤ 358579421647088 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14403 ≤ 358579421647087 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14403 : RowArithmetic 14403 (1111729990070442670399/1000000000000000000000000) (302432540343987928596261/500000000000000000000000) (3397030989429827/500000000000000000000000) where
  r0 := (14463072647/25000000000000000)
  k0 := (438943982443/122070312500000)
  k6 := (5704849083180213/500000000000000000)
  q := (42430826058421252471/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14403]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14403]

theorem width_14404 : mW 14404 = 358666565776801 := by
  have hu : mW 14404 ≤ 358666565776801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14404 ≤ 358666565776800 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14404 : RowArithmetic 14404 (1111701401879162298069/1000000000000000000000000) (604854334005880196079617/1000000000000000000000000) (6792835002674293/1000000000000000000000000) where
  r0 := (289231330429/500000000000000000)
  k0 := (3595641871790947/1000000000000000000)
  k6 := (2852325524856879/250000000000000000)
  q := (169729196074217001519/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14404]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14404]

theorem width_14405 : mW 14405 = 358753725032814 := by
  have hu : mW 14405 ≤ 358753725032814 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14405 ≤ 358753725032813 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14405 : RowArithmetic 14405 (277918205082471245669/250000000000000000000000) (30242179440301266587863/50000000000000000000000) (6791608336212357/1000000000000000000000000) where
  r0 := (144600606573/250000000000000000)
  k0 := (1797727331078479/500000000000000000)
  k6 := (5704453036868987/500000000000000000)
  q := (21216885963778944721/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14405]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14405]

theorem width_14406 : mW 14406 = 358840899416703 := by
  have hu : mW 14406 ≤ 358840899416703 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14406 ≤ 358840899416702 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14406 : RowArithmetic 14406 (555822122710295137361/500000000000000000000000) (604832845088084581184139/1000000000000000000000000) (339519098968673/50000000000000000000000) where
  r0 := (289171101089/500000000000000000)
  k0 := (359526747526221/100000000000000000)
  k6 := (5704255044642321/500000000000000000)
  q := (84870489570874987383/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14406]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14406]

theorem width_14407 : mW 14407 = 358928088930043 := by
  have hu : mW 14407 ≤ 358928088930043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14407 ≤ 358928088930042 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14407 : RowArithmetic 14407 (555807838574629503349/500000000000000000000000) (151205525712932838508943/250000000000000000000000) (271566237282291/40000000000000000000000) where
  r0 := (115656397703/200000000000000000)
  k0 := (1797540155553573/500000000000000000)
  k6 := (2852028536515091/250000000000000000)
  q := (84873435184396772477/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14407]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14407]

theorem width_14408 : mW 14408 = 359015293574410 := by
  have hu : mW 14408 ≤ 359015293574410 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14408 ≤ 359015293574409 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14408 : RowArithmetic 14408 (1111587115513872301339/1000000000000000000000000) (604811362096639204764359/1000000000000000000000000) (3393965097081749/500000000000000000000000) where
  r0 := (578221785299/1000000000000000000)
  k0 := (898723292420721/250000000000000000)
  k6 := (11407718244057987/1000000000000000000)
  q := (6790110455655342283/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14408]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14408]

theorem width_14409 : mW 14409 = 359102513351378 := by
  have hu : mW 14409 ≤ 359102513351378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14409 ≤ 359102513351377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14409 : RowArithmetic 14409 (555779280256206528573/500000000000000000000000) (302400311411240858525503/500000000000000000000000) (6786704765591903/1000000000000000000000000) where
  r0 := (36135099533/62500000000000000)
  k0 := (3594706050986757/1000000000000000000)
  k6 := (5703661191635179/500000000000000000)
  q := (84879326104770648091/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14409]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14409]

theorem width_14410 : mW 14410 = 359189748262523 := by
  have hu : mW 14410 ≤ 359189748262523 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14410 ≤ 359189748262522 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14410 : RowArithmetic 14410 (1111530012142863966903/1000000000000000000000000) (120957977005786518828823/200000000000000000000000) (1696369911560567/250000000000000000000000) where
  r0 := (578101410201/1000000000000000000)
  k0 := (898629738754801/250000000000000000)
  k6 := (11406926563690327/1000000000000000000)
  q := (10610283926455502727/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14410]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14410]

theorem width_14411 : mW 14411 = 359276998309421 := by
  have hu : mW 14411 ≤ 359276998309421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14411 ≤ 359276998309420 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14411 : RowArithmetic 14411 (1111501470403208508429/1000000000000000000000000) (37798696794729103285889/62500000000000000000000) (6784254836014409/1000000000000000000000000) where
  r0 := (578041238313/1000000000000000000)
  k0 := (3594331881768231/1000000000000000000)
  k6 := (2281306157062149/200000000000000000)
  q := (169770433232645077091/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14411]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14411]

theorem width_14412 : mW 14412 = 359364263493648 := by
  have hu : mW 14412 ≤ 359364263493648 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14412 ≤ 359364263493647 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14412 : RowArithmetic 14412 (1111472935291430944183/1000000000000000000000000) (75596051735294346373687/125000000000000000000000) (847878791851023/125000000000000000000000) where
  r0 := (577981076863/1000000000000000000)
  k0 := (143765793249371/40000000000000000)
  k6 := (2281227009624893/200000000000000000)
  q := (84888161718816835267/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14412]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14412]

theorem width_14413 : mW 14413 = 359451543816778 := by
  have hu : mW 14413 ≤ 359451543816778 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14413 ≤ 359451543816777 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14413 : RowArithmetic 14413 (111144440680551730921/100000000000000000000000) (1511894201321685056253/2500000000000000000000) (1695451535630883/250000000000000000000000) where
  r0 := (72240115731/125000000000000000)
  k0 := (1796978901705777/500000000000000000)
  k6 := (5702869676062171/500000000000000000)
  q := (169782213438275094247/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14413]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14413]

theorem width_14414 : mW 14414 = 359538839280388 := by
  have hu : mW 14414 ≤ 359538839280388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14414 ≤ 359538839280387 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14414 : RowArithmetic 14414 (1111415884943452938893/1000000000000000000000000) (120949389730859495433509/200000000000000000000000) (1695145564765093/250000000000000000000000) where
  r0 := (288930392633/500000000000000000)
  k0 := (898442699574349/250000000000000000)
  k6 := (178208495270363/15625000000000000)
  q := (21223512904323826853/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14414]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14414]

theorem width_14415 : mW 14415 = 359626149886053 := by
  have hu : mW 14415 ≤ 359626149886053 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14415 ≤ 359626149886052 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14415 : RowArithmetic 14415 (222277473940644988083/200000000000000000000000) (151184054564724833634531/250000000000000000000000) (3389679342159351/500000000000000000000000) where
  r0 := (288900327557/500000000000000000)
  k0 := (3593583815886017/1000000000000000000)
  k6 := (11404948083653993/1000000000000000000)
  q := (42448498206650373793/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14415]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14415]

theorem width_14416 : mW 14416 = 359713475635350 := by
  have hu : mW 14416 ≤ 359713475635350 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14416 ≤ 359713475635349 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14416 : RowArithmetic 14416 (1111358861082820216077/1000000000000000000000000) (604725489342153903407899/1000000000000000000000000) (3389067709099263/500000000000000000000000) where
  r0 := (577740535389/1000000000000000000)
  k0 := (359339685617163/100000000000000000)
  k6 := (2280910502233897/200000000000000000)
  q := (169799882214328994511/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14416]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14416]

theorem width_14417 : mW 14417 = 359800816529853 := by
  have hu : mW 14417 ≤ 359800816529853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14417 ≤ 359800816529852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14417 : RowArithmetic 14417 (277832589770056982943/250000000000000000000000) (604714761903735555704209/1000000000000000000000000) (6776912460599941/1000000000000000000000000) where
  r0 := (577680426089/1000000000000000000)
  k0 := (3593209919151559/1000000000000000000)
  k6 := (1140415697984257/100000000000000000)
  q := (169805771397794368373/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14417]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14417]

theorem width_14418 : mW 14418 = 359888172571140 := by
  have hu : mW 14418 ≤ 359888172571140 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14418 ≤ 359888172571139 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14418 : RowArithmetic 14418 (1111301863693436061373/1000000000000000000000000) (604704035943318831178611/1000000000000000000000000) (1693922452855753/250000000000000000000000) where
  r0 := (144405081803/250000000000000000)
  k0 := (1796511502411563/500000000000000000)
  k6 := (178183773276033/15625000000000000)
  q := (42452915094254717151/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14418]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14418]

theorem width_14419 : mW 14419 = 359975543760785 := by
  have hu : mW 14419 ≤ 359975543760785 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14419 ≤ 359975543760784 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14419 : RowArithmetic 14419 (1111273374920435334137/1000000000000000000000000) (3779333196628614499237/6250000000000000000000) (3387233735283959/500000000000000000000000) where
  r0 := (288780119377/500000000000000000)
  k0 := (359283611317743/100000000000000000)
  k6 := (5701683020316487/500000000000000000)
  q := (21227193644002967921/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14419]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14419]

theorem width_14420 : mW 14420 = 360062930100365 := by
  have hu : mW 14420 ≤ 360062930100365 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14420 ≤ 360062930100364 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14420 : RowArithmetic 14420 (555622446379607890443/500000000000000000000000) (120936517691037737588137/200000000000000000000000) (846655679741853/125000000000000000000000) where
  r0 := (288750080357/500000000000000000)
  k0 := (1796324622107451/500000000000000000)
  k6 := (456118825309441/40000000000000000)
  q := (169823437722830237141/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14420]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14420]

theorem width_14421 : mW 14421 = 360150331591456 := by
  have hu : mW 14421 ≤ 360150331591456 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14421 ≤ 360150331591455 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14421 : RowArithmetic 14421 (1111216417207768706917/1000000000000000000000000) (120934373385364947447793/200000000000000000000000) (6772023713423953/1000000000000000000000000) where
  r0 := (577440093089/1000000000000000000)
  k0 := (898115599482437/250000000000000000)
  k6 := (11402575265968133/1000000000000000000)
  q := (169829326089459590719/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14421]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14421]

theorem width_14422 : mW 14422 = 360237748235634 := by
  have hu : mW 14422 ≤ 360237748235634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14422 ≤ 360237748235633 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14422 : RowArithmetic 14422 (138898493533010774779/125000000000000000000000) (302330573437580697337233/500000000000000000000000) (6770802296935567/1000000000000000000000000) where
  r0 := (144345008969/250000000000000000)
  k0 := (143691022972647/40000000000000000)
  k6 := (1425272492540271/125000000000000000)
  q := (33967042850386608243/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14422]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14422]

theorem width_14423 : mW 14423 = 360325180034476 := by
  have hu : mW 14423 ≤ 360325180034476 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14423 ≤ 360325180034475 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14423 : RowArithmetic 14423 (111115948592616062897/100000000000000000000000) (604650428299873632635259/1000000000000000000000000) (3384790594184977/500000000000000000000000) where
  r0 := (577319989073/1000000000000000000)
  k0 := (1796044386685749/500000000000000000)
  k6 := (5700892327895501/500000000000000000)
  q := (169841102210271822059/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14423]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14423]

theorem width_14424 : mW 14424 = 360412626989556 := by
  have hu : mW 14424 ≤ 360412626989556 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14424 ≤ 360412626989555 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14424 : RowArithmetic 14424 (1111131030191986629931/1000000000000000000000000) (30231985560031827202733/50000000000000000000000) (3384180193813747/500000000000000000000000) where
  r0 := (577259952677/1000000000000000000)
  k0 := (3591901995089921/1000000000000000000)
  k6 := (11401389412367509/1000000000000000000)
  q := (84923494982248581501/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14424]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14424]

theorem width_14425 : mW 14425 = 360500089102453 := by
  have hu : mW 14425 ≤ 360500089102453 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14425 ≤ 360500089102452 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14425 : RowArithmetic 14425 (1111102581059557150941/1000000000000000000000000) (151157248894281319058179/250000000000000000000000) (1691784973652129/250000000000000000000000) where
  r0 := (288599963343/500000000000000000)
  k0 := (897928809867189/250000000000000000)
  k6 := (2850248552511141/250000000000000000)
  q := (169852877514630290117/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14425]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14425]

theorem width_14426 : mW 14426 = 360587566374742 := by
  have hu : mW 14426 ≤ 360587566374742 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14426 ≤ 360587566374741 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14426 : RowArithmetic 14426 (138884267315858486211/125000000000000000000000) (604618281429015159150469/1000000000000000000000000) (845739963651683/125000000000000000000000) where
  r0 := (577139911097/1000000000000000000)
  k0 := (897882126625551/250000000000000000)
  k6 := (2280119809763009/200000000000000000)
  q := (33971752972138485159/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14426]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14426]

theorem width_14427 : mW 14427 = 360675058807999 := by
  have hu : mW 14427 ≤ 360675058807999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14427 ≤ 360675058807998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14427 : RowArithmetic 14427 (111104570259191483043/100000000000000000000000) (302303784377990775183203/500000000000000000000000) (6764699831342803/1000000000000000000000000) where
  r0 := (144269976477/250000000000000000)
  k0 := (448917724523447/125000000000000000)
  k6 := (11400203928671831/1000000000000000000)
  q := (10616540750169049297/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14427]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14427]

theorem width_14428 : mW 14428 = 360762566403801 := by
  have hu : mW 14428 ≤ 360762566403801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14428 ≤ 360762566403800 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14428 : RowArithmetic 14428 (555508636626347122297/500000000000000000000000) (302298428778849966286821/500000000000000000000000) (3381740130448511/500000000000000000000000) where
  r0 := (144254977779/250000000000000000)
  k0 := (3591155108519069/1000000000000000000)
  k6 := (5699904424803901/500000000000000000)
  q := (84935269470344297013/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14428]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14428]

theorem width_14429 : mW 14429 = 360850089163724 := by
  have hu : mW 14429 ≤ 360850089163724 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14429 ≤ 360850089163723 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14429 : RowArithmetic 14429 (555494425253601836679/500000000000000000000000) (302293073916922957437757/500000000000000000000000) (3381130498888333/500000000000000000000000) where
  r0 := (288479963359/500000000000000000)
  k0 := (3590968443490879/1000000000000000000)
  k6 := (71246336322599/6250000000000000)
  q := (169876425674665052979/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14429]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14429]

theorem width_14430 : mW 14430 = 360937627089346 := by
  have hu : mW 14430 ≤ 360937627089346 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14430 ≤ 360937627089345 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14430 : RowArithmetic 14430 (277740108588360113473/250000000000000000000000) (151143859896023783106093/250000000000000000000000) (6761042041882283/1000000000000000000000000) where
  r0 := (576899952713/1000000000000000000)
  k0 := (143631272044137/40000000000000000)
  k6 := (1139901881468883/100000000000000000)
  q := (84941156102327686649/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14430]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14430]

theorem width_14431 : mW 14431 = 361025180182242 := by
  have hu : mW 14431 ≤ 361025180182242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14431 ≤ 361025180182241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14431 : RowArithmetic 14431 (1110932024789404173921/1000000000000000000000000) (120912946561624668537123/200000000000000000000000) (6759823393114521/1000000000000000000000000) where
  r0 := (576839989097/1000000000000000000)
  k0 := (897648795336947/250000000000000000)
  k6 := (5699311929409829/500000000000000000)
  q := (169888198530680758997/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14431]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14431]

theorem width_14432 : mW 14432 = 361112748443989 := by
  have hu : mW 14432 ≤ 361112748443989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14432 ≤ 361112748443988 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14432 : RowArithmetic 14432 (555451810906547108191/500000000000000000000000) (151138506876401625068401/250000000000000000000000) (3379302525687013/500000000000000000000000) where
  r0 := (576780035869/1000000000000000000)
  k0 := (718081716844877/200000000000000000)
  k6 := (2849557236000303/250000000000000000)
  q := (33978816930552482083/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14432]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14432]

theorem width_14433 : mW 14433 = 361200331876165 := by
  have hu : mW 14433 ≤ 361200331876165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14433 ≤ 361200331876164 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14433 : RowArithmetic 14433 (1110875225422510251213/1000000000000000000000000) (302271661838110258996837/500000000000000000000000) (675738701656147/100000000000000000000000) where
  r0 := (23068803721/40000000000000000)
  k0 := (718044401944859/200000000000000000)
  k6 := (11397834070226379/1000000000000000000)
  q := (169899970570921524219/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14433]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14433]

theorem width_14434 : mW 14434 = 361287930480345 := by
  have hu : mW 14434 ≤ 361287930480345 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14434 ≤ 361287930480344 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14434 : RowArithmetic 14434 (1110846835615654195951/1000000000000000000000000) (120906524263928289656787/200000000000000000000000) (6756169288577617/1000000000000000000000000) where
  r0 := (576660160563/1000000000000000000)
  k0 := (1795017728922409/500000000000000000)
  k6 := (11397439237488053/1000000000000000000)
  q := (33981171257035858681/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14434]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14434]

theorem width_14435 : mW 14435 = 361375544258107 := by
  have hu : mW 14435 ≤ 361375544258107 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14435 ≤ 361375544258106 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14435 : RowArithmetic 14435 (555409226195263636783/500000000000000000000000) (75565240054443185444663/125000000000000000000000) (6754951867323219/1000000000000000000000000) where
  r0 := (7207502981/12500000000000000)
  k0 := (3589848928580143/1000000000000000000)
  k6 := (2849261111444781/250000000000000000)
  q := (84955870897778453649/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14435]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14435]

theorem width_14436 : mW 14436 = 361463173211027 := by
  have hu : mW 14436 ≤ 361463173211027 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14436 ≤ 361463173211026 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14436 : RowArithmetic 14436 (555395037872566231527/500000000000000000000000) (302255610511804448318099/500000000000000000000000) (6753734752699103/1000000000000000000000000) where
  r0 := (23061613071/40000000000000000)
  k0 := (3589662421930683/1000000000000000000)
  k6 := (11396649695092489/1000000000000000000)
  q := (33983525420415110311/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14436]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14436]

theorem width_14437 : mW 14437 = 361550817340682 := by
  have hu : mW 14437 ≤ 361550817340682 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14437 ≤ 361550817340681 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14437 : RowArithmetic 14437 (555380852838736514429/500000000000000000000000) (75562565385438502550259/125000000000000000000000) (168812948615153/25000000000000000000000) where
  r0 := (144120106361/250000000000000000)
  k0 := (897368984471877/250000000000000000)
  k6 := (5698127492710521/500000000000000000)
  q := (1062021951279727551/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14437]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14437]

theorem width_14438 : mW 14438 = 361638476648651 := by
  have hu : mW 14438 ≤ 361638476648651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14438 ≤ 361638476648650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14438 : RowArithmetic 14438 (138841667773194004031/125000000000000000000000) (3778061416343245768269/6250000000000000000000) (42195634018407/6250000000000000000000) where
  r0 := (115284106897/200000000000000000)
  k0 := (897322369111979/250000000000000000)
  k6 := (11395860316757683/1000000000000000000)
  q := (84964698551810327717/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14438]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14438]

theorem width_14439 : mW 14439 = 361726151136508 := by
  have hu : mW 14439 ≤ 361726151136508 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14439 ≤ 361726151136507 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14439 : RowArithmetic 14439 (1110704985267375756003/1000000000000000000000000) (604479131617519373641233/1000000000000000000000000) (6750085247617089/1000000000000000000000000) where
  r0 := (72045081737/125000000000000000)
  k0 := (1794551518804601/500000000000000000)
  k6 := (1139546568909531/100000000000000000)
  q := (42483820449672367007/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14439]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14439]

theorem width_14440 : mW 14440 = 361813840805832 := by
  have hu : mW 14440 ≤ 361813840805832 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14440 ≤ 361813840805831 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14440 : RowArithmetic 14440 (1110676634920948810927/1000000000000000000000000) (604468438090984786945191/1000000000000000000000000) (6748869358522961/1000000000000000000000000) where
  r0 := (576300783673/1000000000000000000)
  k0 := (717783324272487/200000000000000000)
  k6 := (455802844097073/40000000000000000)
  q := (5310661446562000529/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14440]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14440]

theorem width_14441 : mW 14441 = 361901545658200 := by
  have hu : mW 14441 ≤ 361901545658200 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14441 ≤ 361901545658199 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14441 : RowArithmetic 14441 (138831036393034695091/125000000000000000000000) (302228873017496182951741/500000000000000000000000) (1349530755112749/200000000000000000000000) where
  r0 := (115248184763/200000000000000000)
  k0 := (179436511385401/50000000000000000)
  k6 := (11394676556745131/1000000000000000000)
  q := (42486762644381367363/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14441]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14441]

theorem width_14442 : mW 14442 = 361989265695189 := by
  have hu : mW 14442 ≤ 361989265695189 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14442 ≤ 361989265695188 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14442 : RowArithmetic 14442 (138827494241921142851/125000000000000000000000) (302223527724609459225409/500000000000000000000000) (674643849864049/100000000000000000000000) where
  r0 := (576181074319/1000000000000000000)
  k0 := (717708771328027/200000000000000000)
  k6 := (11394282052043133/1000000000000000000)
  q := (169952934661334989259/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14442]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14442]

theorem width_14443 : mW 14443 = 362077000918376 := by
  have hu : mW 14443 ≤ 362077000918376 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14443 ≤ 362077000918375 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14443 : RowArithmetic 14443 (1110591623292231467879/1000000000000000000000000) (604436366333341439591151/1000000000000000000000000) (421576470478393/62500000000000000000000) where
  r0 := (288060617591/500000000000000000)
  k0 := (1794178754076479/500000000000000000)
  k6 := (11393887588313737/1000000000000000000)
  q := (169958818541433736339/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14443]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14443]

theorem width_14444 : mW 14444 = 362164751329338 := by
  have hu : mW 14444 ≤ 362164751329338 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14444 ≤ 362164751329337 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14444 : RowArithmetic 14444 (44422531968514928783/40000000000000000000000) (604425678687036928157827/1000000000000000000000000) (6744008862506267/1000000000000000000000000) where
  r0 := (288030703201/500000000000000000)
  k0 := (3588171182243777/1000000000000000000)
  k6 := (2848373291387463/250000000000000000)
  q := (169964702217842867023/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14444]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14444]

theorem width_14445 : mW 14445 = 362252516929654 := by
  have hu : mW 14445 ≤ 362252516929654 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14445 ≤ 362252516929653 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14445 : RowArithmetic 14445 (222106996339060575681/200000000000000000000000) (604414992509982526621923/1000000000000000000000000) (3371397251548781/500000000000000000000000) where
  r0 := (576001587977/1000000000000000000)
  k0 := (3587984878909881/1000000000000000000)
  k6 := (2848274695936097/250000000000000000)
  q := (84985292845291766989/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14445]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14445]

theorem width_14446 : mW 14446 = 362340297720900 := by
  have hu : mW 14446 ≤ 362340297720900 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14446 ≤ 362340297720899 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14446 : RowArithmetic 14446 (1110506670737531161497/1000000000000000000000000) (302202153900927735132073/500000000000000000000000) (33707902246647/5000000000000000000000) where
  r0 := (8999090311/15625000000000000)
  k0 := (3587798598145443/1000000000000000000)
  k6 := (712044027680641/62500000000000000)
  q := (42494117239919221553/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14446]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14446]

theorem width_14447 : mW 14447 = 362428093704653 := by
  have hu : mW 14447 ≤ 362428093704653 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14447 ≤ 362428093704652 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14447 : RowArithmetic 14447 (277619591584392267379/250000000000000000000000) (604393624562333112798507/1000000000000000000000000) (6740366701103031/1000000000000000000000000) where
  r0 := (28794099109/50000000000000000)
  k0 := (3587612339944633/1000000000000000000)
  k6 := (11392310142980369/1000000000000000000)
  q := (10623897001571504317/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14447]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14447]

theorem width_14448 : mW 14448 = 362515904882492 := by
  have hu : mW 14448 ≤ 362515904882492 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14448 ≤ 362515904882491 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14448 : RowArithmetic 14448 (55522503424671370001/50000000000000000000000) (75547867848886610532959/125000000000000000000000) (6739153258319709/1000000000000000000000000) where
  r0 := (287911097401/500000000000000000)
  k0 := (3587426104301621/1000000000000000000)
  k6 := (2847978971001911/250000000000000000)
  q := (169988234887006224247/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14448]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14448]

theorem width_14449 : mW 14449 = 362603731255994 := by
  have hu : mW 14449 ≤ 362603731255994 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14449 ≤ 362603731255993 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14449 : RowArithmetic 14449 (277605444300779674303/250000000000000000000000) (604372262487812306728209/1000000000000000000000000) (6737940120880763/1000000000000000000000000) where
  r0 := (575762417769/1000000000000000000)
  k0 := (717447978243361/200000000000000000)
  k6 := (2847880416491249/250000000000000000)
  q := (33998823509056897953/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14449]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14449]

theorem width_14450 : mW 14450 = 362691572826737 := by
  have hu : mW 14450 ≤ 362691572826737 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14450 ≤ 362691572826736 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14450 : RowArithmetic 14450 (138799186558081973631/125000000000000000000000) (302180791826084498057749/500000000000000000000000) (842090911085943/125000000000000000000000) where
  r0 := (287851325539/500000000000000000)
  k0 := (56047714073193/15625000000000000)
  k6 := (355972734026417/31250000000000000)
  q := 170
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14450]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14450]

theorem width_14451 : mW 14451 = 362779429596298 := by
  have hu : mW 14451 ≤ 362779429596298 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14451 ≤ 362779429596297 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14451 : RowArithmetic 14451 (555182607138026380567/500000000000000000000000) (151087726570960174003247/250000000000000000000000) (6735514761641463/1000000000000000000000000) where
  r0 := (575642894727/1000000000000000000)
  k0 := (3586867532701543/1000000000000000000)
  k6 := (11390733352641609/1000000000000000000)
  q := (170005882251173885669/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14451]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14451]

theorem width_14452 : mW 14452 = 362867301566255 := by
  have hu : mW 14452 ≤ 362867301566255 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14452 ≤ 362867301566254 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14452 : RowArithmetic 14452 (69396058914707748903/62500000000000000000000) (151085057595626312749577/250000000000000000000000) (6734302539643951/1000000000000000000000000) where
  r0 := (71947893589/125000000000000000)
  k0 := (1793340693629713/500000000000000000)
  k6 := (1423792407168339/125000000000000000)
  q := (21251470537353409229/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14452]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14452]

theorem width_14453 : mW 14453 = 362955188738186 := by
  have hu : mW 14453 ≤ 362955188738186 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14453 ≤ 362955188738185 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14453 : RowArithmetic 14453 (222061735508096918439/200000000000000000000000) (120865911189568102166461/200000000000000000000000) (6733090622596477/1000000000000000000000000) where
  r0 := (71940426629/125000000000000000)
  k0 := (896623816089599/250000000000000000)
  k6 := (11389945202953577/1000000000000000000)
  q := (85008823071490643947/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14453]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14453]

theorem width_14454 : mW 14454 = 363043091113669 := by
  have hu : mW 14454 ≤ 363043091113669 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14454 ≤ 363043091113668 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14454 : RowArithmetic 14454 (55514020949477524971/50000000000000000000000) (604318882979524514863803/1000000000000000000000000) (3365939505200277/500000000000000000000000) where
  r0 := (575463687683/1000000000000000000)
  k0 := (1793154581994749/500000000000000000)
  k6 := (1138955118945513/100000000000000000)
  q := (17002352778365704761/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14454]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14454]

theorem width_14455 : mW 14455 = 363131008694281 := by
  have hu : mW 14455 ≤ 363131008694281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14455 ≤ 363131008694280 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14455 : RowArithmetic 14455 (1110252166980538868491/1000000000000000000000000) (604308211477235428561187/1000000000000000000000000) (26922670811831/4000000000000000000000) where
  r0 := (71925496583/125000000000000000)
  k0 := (896530771538281/250000000000000000)
  k6 := (5694578608422149/500000000000000000)
  q := (170029409220875669077/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14455]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14455]

theorem width_14456 : mW 14456 = 363218941481601 := by
  have hu : mW 14456 ≤ 363218941481601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14456 ≤ 363218941481600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14456 : RowArithmetic 14456 (1110223921511466660717/1000000000000000000000000) (302148770720325697936763/500000000000000000000000) (3364728350084819/500000000000000000000000) where
  r0 := (143836066993/250000000000000000)
  k0 := (3585937030843431/1000000000000000000)
  k6 := (11388763285114009/1000000000000000000)
  q := (34007058090931652949/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14456]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14456]

theorem width_14457 : mW 14457 = 363306889477207 := by
  have hu : mW 14457 ≤ 363306889477207 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14457 ≤ 363306889477206 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14457 : RowArithmetic 14457 (1110195682580352092353/1000000000000000000000000) (120857374573890155390277/200000000000000000000000) (6728246001937847/1000000000000000000000000) where
  r0 := (143821143401/250000000000000000)
  k0 := (1792875499027289/500000000000000000)
  k6 := (5694184697128597/500000000000000000)
  q := (10627573217814121463/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14457]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14457]

theorem width_14458 : mW 14458 = 363394852682676 := by
  have hu : mW 14458 ≤ 363394852682676 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14458 ≤ 363394852682675 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14458 : RowArithmetic 14458 (111016745018521463323/100000000000000000000000) (75534525720413988045431/125000000000000000000000) (6727035608164067/1000000000000000000000000) where
  r0 := (287612444779/500000000000000000)
  k0 := (896391246945959/250000000000000000)
  k6 := (2277595108853357/200000000000000000)
  q := (85023526155999905107/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14458]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14458]

theorem width_14459 : mW 14459 = 363482831099588 := by
  have hu : mW 14459 ≤ 363482831099588 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14459 ≤ 363482831099587 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14459 : RowArithmetic 14459 (1110139224324073065059/1000000000000000000000000) (151066385030478327298877/250000000000000000000000) (6725825518749969/1000000000000000000000000) where
  r0 := (575165215831/1000000000000000000)
  k0 := (44817237500317/12500000000000000)
  k6 := (11387581735135717/1000000000000000000)
  q := (170052932935600966659/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14459]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14459]

theorem width_14460 : mW 14460 = 363570824729519 := by
  have hu : mW 14460 ≤ 363570824729519 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14460 ≤ 363570824729518 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14460 : RowArithmetic 14460 (1110111004994948878203/1000000000000000000000000) (151063718986233412168061/250000000000000000000000) (6724615733597341/1000000000000000000000000) where
  r0 := (575105552421/1000000000000000000)
  k0 := (179259651738821/50000000000000000)
  k6 := (2846796991714231/250000000000000000)
  q := (664292239671291057/3906250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14460]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14460]

theorem width_14461 : mW 14461 = 363658833574049 := by
  have hu : mW 14461 ≤ 363658833574049 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14461 ≤ 363658833574048 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14461 : RowArithmetic 14461 (555041396097931194913/500000000000000000000000) (24169768529282060315759/40000000000000000000000) (3361703126303967/500000000000000000000000) where
  r0 := (23001835973/40000000000000000)
  k0 := (1792503546015583/500000000000000000)
  k6 := (2277358847884669/200000000000000000)
  q := (85032346786384768107/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14461]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14461]

theorem width_14462 : mW 14462 = 363746857634756 := by
  have hu : mW 14462 ≤ 363746857634756 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14462 ≤ 363746857634755 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14462 : RowArithmetic 14462 (1110054585924835654419/1000000000000000000000000) (604233551982945776899799/1000000000000000000000000) (6722197075683579/1000000000000000000000000) where
  r0 := (287493128271/500000000000000000)
  k0 := (3584821171789983/1000000000000000000)
  k6 := (5693200276413959/500000000000000000)
  q := (265735271228717397/1562500000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14462]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14462]

theorem width_14463 : mW 14463 = 363834896913218 := by
  have hu : mW 14463 ≤ 363834896913218 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14463 ≤ 363834896913217 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14463 : RowArithmetic 14463 (1110026386179891492847/1000000000000000000000000) (604222892197295279795413/1000000000000000000000000) (3360494101363071/500000000000000000000000) where
  r0 := (574926624067/1000000000000000000)
  k0 := (716927054808157/200000000000000000)
  k6 := (2277201381412717/200000000000000000)
  q := (21259556674587548887/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14463]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14463]

theorem width_14464 : mW 14464 = 363922951411013 := by
  have hu : mW 14464 ≤ 363922951411013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14464 ≤ 363922951411012 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14464 : RowArithmetic 14464 (1109998192959053491969/1000000000000000000000000) (604212233874779012377721/1000000000000000000000000) (3359889816818767/500000000000000000000000) where
  r0 := (5748670019/10000000000000000)
  k0 := (3500438866003/976562500000000)
  k6 := (11385613302123287/1000000000000000000)
  q := (166096028323978897/976562500000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14464]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14464]

theorem width_14465 : mW 14465 = 364011021129720 := by
  have hu : mW 14465 ≤ 364011021129720 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14465 ≤ 364011021129719 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14465 : RowArithmetic 14465 (1109970006260345520341/1000000000000000000000000) (302100788507538025309319/500000000000000000000000) (6718571368319683/1000000000000000000000000) where
  r0 := (574807390037/1000000000000000000)
  k0 := (3584263546019873/1000000000000000000)
  k6 := (11385219737999969/1000000000000000000)
  q := (34017642481512442399/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14465]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14465]

theorem width_14466 : mW 14466 = 364099106070917 := by
  have hu : mW 14466 ≤ 364099106070917 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14466 ≤ 364099106070916 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14466 : RowArithmetic 14466 (1109941826081792696243/1000000000000000000000000) (604190921617865581762777/1000000000000000000000000) (419835212917161/62500000000000000000000) where
  r0 := (143686947119/250000000000000000)
  k0 := (3584077715736449/1000000000000000000)
  k6 := (11384826214686577/1000000000000000000)
  q := (170094091608144931473/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14466]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14466]

theorem width_14467 : mW 14467 = 364187206236184 := by
  have hu : mW 14467 ≤ 364187206236184 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14467 ≤ 364187206236183 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14467 : RowArithmetic 14467 (1109913652421419935751/1000000000000000000000000) (604180267682826873107737/1000000000000000000000000) (1343231149720841/200000000000000000000000) where
  r0 := (287344098607/500000000000000000)
  k0 := (55998311061421/15625000000000000)
  k6 := (11384432732176059/1000000000000000000)
  q := (10631248162845226331/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14467]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14467]

theorem width_14468 : mW 14468 = 364275321627098 := by
  have hu : mW 14468 ≤ 364275321627098 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14468 ≤ 364275321627097 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14468 : RowArithmetic 14468 (22197709705545087419/20000000000000000000000) (120833923041927856848009/200000000000000000000000) (6714948394010653/1000000000000000000000000) where
  r0 := (574628616249/1000000000000000000)
  k0 := (1791853061300309/500000000000000000)
  k6 := (11384039290461363/1000000000000000000)
  q := (170105849399719350157/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14468]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14468]

theorem width_14469 : mW 14469 = 364363452245239 := by
  have hu : mW 14469 ≤ 364363452245239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14469 ≤ 364363452245238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14469 : RowArithmetic 14469 (138732165580915305977/125000000000000000000000) (604158964197982356407767/1000000000000000000000000) (839217667849499/125000000000000000000000) where
  r0 := (287284522789/500000000000000000)
  k0 := (358352035973961/100000000000000000)
  k6 := (11383645889535441/1000000000000000000)
  q := (42527931997688295777/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14469]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14469]

theorem width_14470 : mW 14470 = 364451598092184 := by
  have hu : mW 14470 ≤ 364451598092184 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14470 ≤ 364451598092183 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14470 : RowArithmetic 14470 (277457292632413206601/250000000000000000000000) (18879634832735485204601/31250000000000000000000) (1342506918972477/200000000000000000000000) where
  r0 := (1436273713/2500000000000000)
  k0 := (3583334619348297/1000000000000000000)
  k6 := (5691626264695623/500000000000000000)
  q := (85058803189323090781/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14470]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14470]

theorem width_14471 : mW 14471 = 364539759169514 := by
  have hu : mW 14471 ≤ 364539759169514 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14471 ≤ 364539759169513 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14471 : RowArithmetic 14471 (1109801022922272998313/1000000000000000000000000) (120827533311595710791429/200000000000000000000000) (3355664075055981/500000000000000000000000) where
  r0 := (574449935111/1000000000000000000)
  k0 := (1791574450708849/500000000000000000)
  k6 := (2845714802505433/250000000000000000)
  q := (170123484563419403293/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14471]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14471]

theorem width_14472 : mW 14472 = 364627935478806 := by
  have hu : mW 14472 ≤ 364627935478806 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14472 ≤ 364627935478805 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14472 : RowArithmetic 14472 (55488644091160657531/50000000000000000000000) (604127019928991090440813/1000000000000000000000000) (6710122008446967/1000000000000000000000000) where
  r0 := (143597598827/250000000000000000)
  k0 := (895740801485487/250000000000000000)
  k6 := (2276493186283971/200000000000000000)
  q := (42532340636273475609/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14472]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14472]

theorem width_14473 : mW 14473 = 364716127021640 := by
  have hu : mW 14473 ≤ 364716127021640 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14473 ≤ 364716127021639 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14473 : RowArithmetic 14473 (1109744747230502785099/1000000000000000000000000) (604116374760253104193403/1000000000000000000000000) (1677229042442407/250000000000000000000000) where
  r0 := (574330865791/1000000000000000000)
  k0 := (179138876646227/50000000000000000)
  k6 := (5691036346789287/500000000000000000)
  q := (170135240323690729491/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14473]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14473]

theorem width_14474 : mW 14474 = 364804333799594 := by
  have hu : mW 14474 ≤ 364804333799594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14474 ≤ 364804333799593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14474 : RowArithmetic 14474 (554858309571086565787/500000000000000000000000) (604105731051444476511083/1000000000000000000000000) (6707710633982247/1000000000000000000000000) where
  r0 := (114854269311/200000000000000000)
  k0 := (3582591882353369/1000000000000000000)
  k6 := (11381679496490847/1000000000000000000)
  q := (4253527947480773283/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14474]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14474]

theorem width_14475 : mW 14475 = 364892555814248 := by
  have hu : mW 14475 ≤ 364892555814248 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14475 ≤ 364892555814247 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14475 : RowArithmetic 14475 (554844248778127608857/500000000000000000000000) (604095088802245283998227/1000000000000000000000000) (6706505400987133/1000000000000000000000000) where
  r0 := (574211837599/1000000000000000000)
  k0 := (895601563557201/250000000000000000)
  k6 := (2845321585037409/250000000000000000)
  q := (10634187204483471947/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14475]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14475]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14401 then ⟨(555893593193547918209/500000000000000000000000), (604886578500196844768163/1000000000000000000000000), (3398258430401151/500000000000000000000000)⟩ else
  if n = 14402 then ⟨(1111758584905746343421/1000000000000000000000000), (604875828852639116081649/1000000000000000000000000), (1698822316217207/250000000000000000000000)⟩ else
  if n = 14403 then ⟨(1111729990070442670399/1000000000000000000000000), (302432540343987928596261/500000000000000000000000), (3397030989429827/500000000000000000000000)⟩ else
  if n = 14404 then ⟨(1111701401879162298069/1000000000000000000000000), (604854334005880196079617/1000000000000000000000000), (6792835002674293/1000000000000000000000000)⟩ else
  if n = 14405 then ⟨(277918205082471245669/250000000000000000000000), (30242179440301266587863/50000000000000000000000), (6791608336212357/1000000000000000000000000)⟩ else
  if n = 14406 then ⟨(555822122710295137361/500000000000000000000000), (604832845088084581184139/1000000000000000000000000), (339519098968673/50000000000000000000000)⟩ else
  if n = 14407 then ⟨(555807838574629503349/500000000000000000000000), (151205525712932838508943/250000000000000000000000), (271566237282291/40000000000000000000000)⟩ else
  if n = 14408 then ⟨(1111587115513872301339/1000000000000000000000000), (604811362096639204764359/1000000000000000000000000), (3393965097081749/500000000000000000000000)⟩ else
  if n = 14409 then ⟨(555779280256206528573/500000000000000000000000), (302400311411240858525503/500000000000000000000000), (6786704765591903/1000000000000000000000000)⟩ else
  if n = 14410 then ⟨(1111530012142863966903/1000000000000000000000000), (120957977005786518828823/200000000000000000000000), (1696369911560567/250000000000000000000000)⟩ else
  if n = 14411 then ⟨(1111501470403208508429/1000000000000000000000000), (37798696794729103285889/62500000000000000000000), (6784254836014409/1000000000000000000000000)⟩ else
  if n = 14412 then ⟨(1111472935291430944183/1000000000000000000000000), (75596051735294346373687/125000000000000000000000), (847878791851023/125000000000000000000000)⟩ else
  if n = 14413 then ⟨(111144440680551730921/100000000000000000000000), (1511894201321685056253/2500000000000000000000), (1695451535630883/250000000000000000000000)⟩ else
  if n = 14414 then ⟨(1111415884943452938893/1000000000000000000000000), (120949389730859495433509/200000000000000000000000), (1695145564765093/250000000000000000000000)⟩ else
  if n = 14415 then ⟨(222277473940644988083/200000000000000000000000), (151184054564724833634531/250000000000000000000000), (3389679342159351/500000000000000000000000)⟩ else
  if n = 14416 then ⟨(1111358861082820216077/1000000000000000000000000), (604725489342153903407899/1000000000000000000000000), (3389067709099263/500000000000000000000000)⟩ else
  if n = 14417 then ⟨(277832589770056982943/250000000000000000000000), (604714761903735555704209/1000000000000000000000000), (6776912460599941/1000000000000000000000000)⟩ else
  if n = 14418 then ⟨(1111301863693436061373/1000000000000000000000000), (604704035943318831178611/1000000000000000000000000), (1693922452855753/250000000000000000000000)⟩ else
  if n = 14419 then ⟨(1111273374920435334137/1000000000000000000000000), (3779333196628614499237/6250000000000000000000), (3387233735283959/500000000000000000000000)⟩ else
  if n = 14420 then ⟨(555622446379607890443/500000000000000000000000), (120936517691037737588137/200000000000000000000000), (846655679741853/125000000000000000000000)⟩ else
  if n = 14421 then ⟨(1111216417207768706917/1000000000000000000000000), (120934373385364947447793/200000000000000000000000), (6772023713423953/1000000000000000000000000)⟩ else
  if n = 14422 then ⟨(138898493533010774779/125000000000000000000000), (302330573437580697337233/500000000000000000000000), (6770802296935567/1000000000000000000000000)⟩ else
  if n = 14423 then ⟨(111115948592616062897/100000000000000000000000), (604650428299873632635259/1000000000000000000000000), (3384790594184977/500000000000000000000000)⟩ else
  if n = 14424 then ⟨(1111131030191986629931/1000000000000000000000000), (30231985560031827202733/50000000000000000000000), (3384180193813747/500000000000000000000000)⟩ else
  if n = 14425 then ⟨(1111102581059557150941/1000000000000000000000000), (151157248894281319058179/250000000000000000000000), (1691784973652129/250000000000000000000000)⟩ else
  if n = 14426 then ⟨(138884267315858486211/125000000000000000000000), (604618281429015159150469/1000000000000000000000000), (845739963651683/125000000000000000000000)⟩ else
  if n = 14427 then ⟨(111104570259191483043/100000000000000000000000), (302303784377990775183203/500000000000000000000000), (6764699831342803/1000000000000000000000000)⟩ else
  if n = 14428 then ⟨(555508636626347122297/500000000000000000000000), (302298428778849966286821/500000000000000000000000), (3381740130448511/500000000000000000000000)⟩ else
  if n = 14429 then ⟨(555494425253601836679/500000000000000000000000), (302293073916922957437757/500000000000000000000000), (3381130498888333/500000000000000000000000)⟩ else
  if n = 14430 then ⟨(277740108588360113473/250000000000000000000000), (151143859896023783106093/250000000000000000000000), (6761042041882283/1000000000000000000000000)⟩ else
  if n = 14431 then ⟨(1110932024789404173921/1000000000000000000000000), (120912946561624668537123/200000000000000000000000), (6759823393114521/1000000000000000000000000)⟩ else
  if n = 14432 then ⟨(555451810906547108191/500000000000000000000000), (151138506876401625068401/250000000000000000000000), (3379302525687013/500000000000000000000000)⟩ else
  if n = 14433 then ⟨(1110875225422510251213/1000000000000000000000000), (302271661838110258996837/500000000000000000000000), (675738701656147/100000000000000000000000)⟩ else
  if n = 14434 then ⟨(1110846835615654195951/1000000000000000000000000), (120906524263928289656787/200000000000000000000000), (6756169288577617/1000000000000000000000000)⟩ else
  if n = 14435 then ⟨(555409226195263636783/500000000000000000000000), (75565240054443185444663/125000000000000000000000), (6754951867323219/1000000000000000000000000)⟩ else
  if n = 14436 then ⟨(555395037872566231527/500000000000000000000000), (302255610511804448318099/500000000000000000000000), (6753734752699103/1000000000000000000000000)⟩ else
  if n = 14437 then ⟨(555380852838736514429/500000000000000000000000), (75562565385438502550259/125000000000000000000000), (168812948615153/25000000000000000000000)⟩ else
  if n = 14438 then ⟨(138841667773194004031/125000000000000000000000), (3778061416343245768269/6250000000000000000000), (42195634018407/6250000000000000000000)⟩ else
  if n = 14439 then ⟨(1110704985267375756003/1000000000000000000000000), (604479131617519373641233/1000000000000000000000000), (6750085247617089/1000000000000000000000000)⟩ else
  if n = 14440 then ⟨(1110676634920948810927/1000000000000000000000000), (604468438090984786945191/1000000000000000000000000), (6748869358522961/1000000000000000000000000)⟩ else
  if n = 14441 then ⟨(138831036393034695091/125000000000000000000000), (302228873017496182951741/500000000000000000000000), (1349530755112749/200000000000000000000000)⟩ else
  if n = 14442 then ⟨(138827494241921142851/125000000000000000000000), (302223527724609459225409/500000000000000000000000), (674643849864049/100000000000000000000000)⟩ else
  if n = 14443 then ⟨(1110591623292231467879/1000000000000000000000000), (604436366333341439591151/1000000000000000000000000), (421576470478393/62500000000000000000000)⟩ else
  if n = 14444 then ⟨(44422531968514928783/40000000000000000000000), (604425678687036928157827/1000000000000000000000000), (6744008862506267/1000000000000000000000000)⟩ else
  if n = 14445 then ⟨(222106996339060575681/200000000000000000000000), (604414992509982526621923/1000000000000000000000000), (3371397251548781/500000000000000000000000)⟩ else
  if n = 14446 then ⟨(1110506670737531161497/1000000000000000000000000), (302202153900927735132073/500000000000000000000000), (33707902246647/5000000000000000000000)⟩ else
  if n = 14447 then ⟨(277619591584392267379/250000000000000000000000), (604393624562333112798507/1000000000000000000000000), (6740366701103031/1000000000000000000000000)⟩ else
  if n = 14448 then ⟨(55522503424671370001/50000000000000000000000), (75547867848886610532959/125000000000000000000000), (6739153258319709/1000000000000000000000000)⟩ else
  if n = 14449 then ⟨(277605444300779674303/250000000000000000000000), (604372262487812306728209/1000000000000000000000000), (6737940120880763/1000000000000000000000000)⟩ else
  if n = 14450 then ⟨(138799186558081973631/125000000000000000000000), (302180791826084498057749/500000000000000000000000), (842090911085943/125000000000000000000000)⟩ else
  if n = 14451 then ⟨(555182607138026380567/500000000000000000000000), (151087726570960174003247/250000000000000000000000), (6735514761641463/1000000000000000000000000)⟩ else
  if n = 14452 then ⟨(69396058914707748903/62500000000000000000000), (151085057595626312749577/250000000000000000000000), (6734302539643951/1000000000000000000000000)⟩ else
  if n = 14453 then ⟨(222061735508096918439/200000000000000000000000), (120865911189568102166461/200000000000000000000000), (6733090622596477/1000000000000000000000000)⟩ else
  if n = 14454 then ⟨(55514020949477524971/50000000000000000000000), (604318882979524514863803/1000000000000000000000000), (3365939505200277/500000000000000000000000)⟩ else
  if n = 14455 then ⟨(1110252166980538868491/1000000000000000000000000), (604308211477235428561187/1000000000000000000000000), (26922670811831/4000000000000000000000)⟩ else
  if n = 14456 then ⟨(1110223921511466660717/1000000000000000000000000), (302148770720325697936763/500000000000000000000000), (3364728350084819/500000000000000000000000)⟩ else
  if n = 14457 then ⟨(1110195682580352092353/1000000000000000000000000), (120857374573890155390277/200000000000000000000000), (6728246001937847/1000000000000000000000000)⟩ else
  if n = 14458 then ⟨(111016745018521463323/100000000000000000000000), (75534525720413988045431/125000000000000000000000), (6727035608164067/1000000000000000000000000)⟩ else
  if n = 14459 then ⟨(1110139224324073065059/1000000000000000000000000), (151066385030478327298877/250000000000000000000000), (6725825518749969/1000000000000000000000000)⟩ else
  if n = 14460 then ⟨(1110111004994948878203/1000000000000000000000000), (151063718986233412168061/250000000000000000000000), (6724615733597341/1000000000000000000000000)⟩ else
  if n = 14461 then ⟨(555041396097931194913/500000000000000000000000), (24169768529282060315759/40000000000000000000000), (3361703126303967/500000000000000000000000)⟩ else
  if n = 14462 then ⟨(1110054585924835654419/1000000000000000000000000), (604233551982945776899799/1000000000000000000000000), (6722197075683579/1000000000000000000000000)⟩ else
  if n = 14463 then ⟨(1110026386179891492847/1000000000000000000000000), (604222892197295279795413/1000000000000000000000000), (3360494101363071/500000000000000000000000)⟩ else
  if n = 14464 then ⟨(1109998192959053491969/1000000000000000000000000), (604212233874779012377721/1000000000000000000000000), (3359889816818767/500000000000000000000000)⟩ else
  if n = 14465 then ⟨(1109970006260345520341/1000000000000000000000000), (302100788507538025309319/500000000000000000000000), (6718571368319683/1000000000000000000000000)⟩ else
  if n = 14466 then ⟨(1109941826081792696243/1000000000000000000000000), (604190921617865581762777/1000000000000000000000000), (419835212917161/62500000000000000000000)⟩ else
  if n = 14467 then ⟨(1109913652421419935751/1000000000000000000000000), (604180267682826873107737/1000000000000000000000000), (1343231149720841/200000000000000000000000)⟩ else
  if n = 14468 then ⟨(22197709705545087419/20000000000000000000000), (120833923041927856848009/200000000000000000000000), (6714948394010653/1000000000000000000000000)⟩ else
  if n = 14469 then ⟨(138732165580915305977/125000000000000000000000), (604158964197982356407767/1000000000000000000000000), (839217667849499/125000000000000000000000)⟩ else
  if n = 14470 then ⟨(277457292632413206601/250000000000000000000000), (18879634832735485204601/31250000000000000000000), (1342506918972477/200000000000000000000000)⟩ else
  if n = 14471 then ⟨(1109801022922272998313/1000000000000000000000000), (120827533311595710791429/200000000000000000000000), (3355664075055981/500000000000000000000000)⟩ else
  if n = 14472 then ⟨(55488644091160657531/50000000000000000000000), (604127019928991090440813/1000000000000000000000000), (6710122008446967/1000000000000000000000000)⟩ else
  if n = 14473 then ⟨(1109744747230502785099/1000000000000000000000000), (604116374760253104193403/1000000000000000000000000), (1677229042442407/250000000000000000000000)⟩ else
  if n = 14474 then ⟨(554858309571086565787/500000000000000000000000), (604105731051444476511083/1000000000000000000000000), (6707710633982247/1000000000000000000000000)⟩ else
  ⟨(554844248778127608857/500000000000000000000000), (604095088802245283998227/1000000000000000000000000), (6706505400987133/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14401 ≤ n) (hb : n ≤ 14475) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14401
  · exact row_14402
  · exact row_14403
  · exact row_14404
  · exact row_14405
  · exact row_14406
  · exact row_14407
  · exact row_14408
  · exact row_14409
  · exact row_14410
  · exact row_14411
  · exact row_14412
  · exact row_14413
  · exact row_14414
  · exact row_14415
  · exact row_14416
  · exact row_14417
  · exact row_14418
  · exact row_14419
  · exact row_14420
  · exact row_14421
  · exact row_14422
  · exact row_14423
  · exact row_14424
  · exact row_14425
  · exact row_14426
  · exact row_14427
  · exact row_14428
  · exact row_14429
  · exact row_14430
  · exact row_14431
  · exact row_14432
  · exact row_14433
  · exact row_14434
  · exact row_14435
  · exact row_14436
  · exact row_14437
  · exact row_14438
  · exact row_14439
  · exact row_14440
  · exact row_14441
  · exact row_14442
  · exact row_14443
  · exact row_14444
  · exact row_14445
  · exact row_14446
  · exact row_14447
  · exact row_14448
  · exact row_14449
  · exact row_14450
  · exact row_14451
  · exact row_14452
  · exact row_14453
  · exact row_14454
  · exact row_14455
  · exact row_14456
  · exact row_14457
  · exact row_14458
  · exact row_14459
  · exact row_14460
  · exact row_14461
  · exact row_14462
  · exact row_14463
  · exact row_14464
  · exact row_14465
  · exact row_14466
  · exact row_14467
  · exact row_14468
  · exact row_14469
  · exact row_14470
  · exact row_14471
  · exact row_14472
  · exact row_14473
  · exact row_14474
  · exact row_14475

end BstLean.Part271.R3.Rows14401
