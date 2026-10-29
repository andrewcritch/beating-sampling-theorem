import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15035–15109. -/
namespace BstLean.Part271.R3.Rows15035
open Real BstLean.Part130 BstLean.Part227

theorem width_15035 : mW 15035 = 416736954437119 := by
  have hu : mW 15035 ≤ 416736954437119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15035 ≤ 416736954437118 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15035 : RowArithmetic 15035 (1094906785975375015383/1000000000000000000000000) (59835567175862463992233/100000000000000000000000) (3038207331230857/500000000000000000000000) where
  r0 := (542431436889/1000000000000000000)
  k0 := (348185907447001/100000000000000000)
  k6 := (5583659469931493/500000000000000000)
  q := (86703517806372770033/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15035]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15035]

theorem width_15036 : mW 15036 = 416833974763683 := by
  have hu : mW 15036 ≤ 416833974763683 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15036 ≤ 416833974763682 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15036 : RowArithmetic 15036 (273720505603958246093/250000000000000000000000) (299172900306972058214879/500000000000000000000000) (1518841241469077/250000000000000000000000) where
  r0 := (542377324517/1000000000000000000)
  k0 := (3481685396895439/1000000000000000000)
  k6 := (1395868447621281/125000000000000000)
  q := (173412802295562942097/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15036]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15036]

theorem width_15037 : mW 15037 = 416931011222928 := by
  have hu : mW 15037 ≤ 416931011222928 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15037 ≤ 416931011222927 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15037 : RowArithmetic 15037 (547428632179899885999/500000000000000000000000) (37395995672703727566831/62500000000000000000000) (6074315522780469/1000000000000000000000000) where
  r0 := (271161610571/500000000000000000)
  k0 := (3481511739535529/1000000000000000000)
  k6 := (139582203239033/12500000000000000)
  q := (173418568786621001799/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15037]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15037]

theorem width_15038 : mW 15038 = 417028063816462 := by
  have hu : mW 15038 ≤ 417028063816462 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15038 ≤ 417028063816461 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15038 : RowArithmetic 15038 (547416255902837281831/500000000000000000000000) (119665212441260027117931/200000000000000000000000) (3036633166547811/500000000000000000000000) where
  r0 := (13556728169/25000000000000000)
  k0 := (3481338102380463/1000000000000000000)
  k6 := (11166204974314001/1000000000000000000)
  q := (43356083771484711901/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15038]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15038]

theorem width_15039 : mW 15039 = 417125132545895 := by
  have hu : mW 15039 ≤ 417125132545895 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15039 ≤ 417125132545894 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15039 : RowArithmetic 15039 (1094807764751856368531/1000000000000000000000000) (598316194942794489891317/1000000000000000000000000) (3036108698371597/500000000000000000000000) where
  r0 := (542215041371/1000000000000000000)
  k0 := (1740582242716633/500000000000000000)
  k6 := (446633349061527/40000000000000000)
  q := (43357525298383901191/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15039]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15039]

theorem width_15040 : mW 15040 = 417222217412837 := by
  have hu : mW 15040 ≤ 417222217412837 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15040 ≤ 417222217412836 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15040 : RowArithmetic 15040 (1094783023196744792071/1000000000000000000000000) (299153164486235886423889/500000000000000000000000) (6071168713644641/1000000000000000000000000) where
  r0 := (135540241243/250000000000000000)
  k0 := (3480990888687329/1000000000000000000)
  k6 := (11165462515789007/1000000000000000000)
  q := (21679483388678799419/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15040]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15040]

theorem width_15041 : mW 15041 = 417319318418898 := by
  have hu : mW 15041 ≤ 417319318418898 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15041 ≤ 417319318418897 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15041 : RowArithmetic 15041 (547379143569370017881/500000000000000000000000) (598296464295061067199317/1000000000000000000000000) (6070120283721451/1000000000000000000000000) where
  r0 := (542106897561/1000000000000000000)
  k0 := (435102164017407/125000000000000000)
  k6 := (558254567103017/50000000000000000)
  q := (173441632833642338263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15041]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15041]

theorem width_15042 : mW 15042 = 417416435565686 := by
  have hu : mW 15042 ≤ 417416435565686 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15042 ≤ 417416435565685 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15042 : RowArithmetic 15042 (1094733556576243667531/1000000000000000000000000) (119657320182058324287339/200000000000000000000000) (6069072106895171/1000000000000000000000000) where
  r0 := (16939151223/31250000000000000)
  k0 := (696128751157129/200000000000000000)
  k6 := (1395590025668253/125000000000000000)
  q := (43361849591547637303/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15042]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15042]

theorem width_15043 : mW 15043 = 417513568854812 := by
  have hu : mW 15043 ≤ 417513568854812 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15043 ≤ 417513568854811 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15043 : RowArithmetic 15043 (1094708831507656693911/1000000000000000000000000) (119655347763578523911567/200000000000000000000000) (1213604836617467/200000000000000000000000) where
  r0 := (270999394847/500000000000000000)
  k0 := (3480470219619887/1000000000000000000)
  k6 := (2232869821127981/200000000000000000)
  q := (8672658185354707037/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15043]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15043]

theorem width_15044 : mW 15044 = 417610718287886 := by
  have hu : mW 15044 ≤ 417610718287886 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15044 ≤ 417610718287885 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15044 : RowArithmetic 15044 (218936822386276220449/200000000000000000000000) (11965337560351869142453/20000000000000000000000) (3033488256109761/500000000000000000000000) where
  r0 := (108388949847/200000000000000000)
  k0 := (696059340729/200000000000000)
  k6 := (2232795608587167/200000000000000000)
  q := (173458928856372222209/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15044]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15044]

theorem width_15045 : mW 15045 = 417707883866517 := by
  have hu : mW 15045 ≤ 417707883866517 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15045 ≤ 417707883866516 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15045 : RowArithmetic 15045 (1094659397845819859661/1000000000000000000000000) (598257018509123540415493/1000000000000000000000000) (1516482273553339/250000000000000000000000) where
  r0 := (108378143551/200000000000000000)
  k0 := (3480123207851161/1000000000000000000)
  k6 := (11163607017227663/1000000000000000000)
  q := (5420771681688871869/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15045]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15045]

theorem width_15046 : mW 15046 = 417805065592316 := by
  have hu : mW 15046 ≤ 417805065592316 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15046 ≤ 417805065592315 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15046 : RowArithmetic 15046 (273658672312343939433/250000000000000000000000) (598247160292212345500239/1000000000000000000000000) (6064881928990463/1000000000000000000000000) where
  r0 := (135459173813/250000000000000000)
  k0 := (695989946446993/200000000000000000)
  k6 := (2790809007127311/250000000000000000)
  q := (3469409171602565531/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15046]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15046]

theorem width_15047 : mW 15047 = 417902263466891 := by
  have hu : mW 15047 ≤ 417902263466891 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15047 ≤ 417902263466890 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15047 : RowArithmetic 15047 (1094609986140453336777/1000000000000000000000000) (598237303366589496576979/1000000000000000000000000) (303191750823627/50000000000000000000000) where
  r0 := (21671307269/40000000000000000)
  k0 := (3479776276796219/1000000000000000000)
  k6 := (11162865076774431/1000000000000000000)
  q := (10842263947165278267/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15047]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15047]

theorem width_15048 : mW 15048 = 417999477491853 := by
  have hu : mW 15048 ≤ 417999477491853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15048 ≤ 417999477491852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15048 : RowArithmetic 15048 (43783411540698263061/40000000000000000000000) (149556861932996154907261/250000000000000000000000) (242511534263251/40000000000000000000000) where
  r0 := (135432169293/250000000000000000)
  k0 := (869900710382879/250000000000000000)
  k6 := (279062354050427/25000000000000000)
  q := (86740993768805761821/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15048]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15048]

theorem width_15049 : mW 15049 = 418096707668813 := by
  have hu : mW 15049 ≤ 418096707668813 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15049 ≤ 418096707668812 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15049 : RowArithmetic 15049 (547280298189395025509/500000000000000000000000) (299108796694063714134661/500000000000000000000000) (1212348389847677/200000000000000000000000) where
  r0 := (54167468159/100000000000000000)
  k0 := (10873216957607/3125000000000000)
  k6 := (1395265410528881/125000000000000000)
  q := (21685968966131073019/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15049]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15049]

theorem width_15050 : mW 15050 = 418193953999379 := by
  have hu : mW 15050 ≤ 418193953999379 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15050 ≤ 418193953999378 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15050 : RowArithmetic 15050 (68408494357678755053/62500000000000000000000) (299103870167373868318499/500000000000000000000000) (3030347897182829/500000000000000000000000) where
  r0 := (541620694977/1000000000000000000)
  k0 := (3479256031500981/1000000000000000000)
  k6 := (5580876221705097/500000000000000000)
  q := (43373378932243681031/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15050]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15050]

theorem width_15051 : mW 15051 = 418291216485163 := by
  have hu : mW 15051 ≤ 418291216485163 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15051 ≤ 418291216485162 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15051 : RowArithmetic 15051 (1094511228548072042473/1000000000000000000000000) (37387368035723465590529/62500000000000000000000) (6059649891884859/1000000000000000000000000) where
  r0 := (541566717331/1000000000000000000)
  k0 := (347908265672833/100000000000000000)
  k6 := (11161381639548377/1000000000000000000)
  q := (173499279537409030707/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15051]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15051]

theorem width_15052 : mW 15052 = 418388495127774 := by
  have hu : mW 15052 ≤ 418388495127774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15052 ≤ 418388495127773 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15052 : RowArithmetic 15052 (1094486552852833058033/1000000000000000000000000) (598188038098340536678213/1000000000000000000000000) (94665691276841/15625000000000000000000) where
  r0 := (10830254973/20000000000000000)
  k0 := (3478909302112877/1000000000000000000)
  k6 := (5580505436319729/500000000000000000)
  q := (173505043154370587881/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15052]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15052]

theorem width_15053 : mW 15053 = 418485789928823 := by
  have hu : mW 15053 ≤ 418485789928823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15053 ≤ 418485789928822 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15053 : RowArithmetic 15053 (547230941317775037099/500000000000000000000000) (299089094457386524910083/500000000000000000000000) (6057558843786391/1000000000000000000000000) where
  r0 := (135364697233/250000000000000000)
  k0 := (347873596765121/100000000000000000)
  k6 := (11160640142677301/1000000000000000000)
  q := (21688850822484809557/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15053]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15053]

theorem width_15054 : mW 15054 = 418583100889920 := by
  have hu : mW 15054 ≤ 418583100889920 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15054 ≤ 418583100889919 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15054 : RowArithmetic 15054 (1094437217894631014109/1000000000000000000000000) (119633668204120605815561/200000000000000000000000) (3028256849006221/500000000000000000000000) where
  r0 := (21656193527/40000000000000000)
  k0 := (1739281326669959/500000000000000000)
  k6 := (1116026944965577/100000000000000000)
  q := (86758284906975887037/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15054]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15054]

theorem width_15055 : mW 15055 = 418680428012675 := by
  have hu : mW 15055 ≤ 418680428012675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15055 ≤ 418680428012674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15055 : RowArithmetic 15055 (218882511725696878583/200000000000000000000000) (37384905900972547109757/62500000000000000000000) (6055468804317891/1000000000000000000000000) where
  r0 := (541350896377/1000000000000000000)
  k0 := (3478389359175587/1000000000000000000)
  k6 := (1115989879356873/100000000000000000)
  q := (21690291607076194401/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15055]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15055]

theorem width_15056 : mW 15056 = 418777771298699 := by
  have hu : mW 15056 ≤ 418777771298699 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15056 ≤ 418777771298698 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15056 : RowArithmetic 15056 (1094387904835518934213/1000000000000000000000000) (14953716227484412041217/25000000000000000000000) (6054424162624667/1000000000000000000000000) where
  r0 := (33831060221/62500000000000000)
  k0 := (3478216085154803/1000000000000000000)
  k6 := (174367627725157/15625000000000000)
  q := (173528095707870891163/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15056]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15056]

theorem width_15057 : mW 15057 = 418875130749602 := by
  have hu : mW 15057 ≤ 418875130749602 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15057 ≤ 418875130749601 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15057 : RowArithmetic 15057 (218872651302828867353/200000000000000000000000) (5981388050717805150047/10000000000000000000000) (6053379772854743/1000000000000000000000000) where
  r0 := (541243039649/1000000000000000000)
  k0 := (3478042831270937/1000000000000000000)
  k6 := (11159157592173593/1000000000000000000)
  q := (173533858367754850079/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15057]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15057]

theorem width_15058 : mW 15058 = 418972506366995 := by
  have hu : mW 15058 ≤ 418972506366995 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15058 ≤ 418972506366994 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15058 : RowArithmetic 15058 (273584653415692626877/250000000000000000000000) (119625792466500669369899/200000000000000000000000) (1513083908732527/250000000000000000000000) where
  r0 := (108237824943/200000000000000000)
  k0 := (695573919504757/200000000000000000)
  k6 := (2231757409370647/200000000000000000)
  q := (173539620836280496929/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15058]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15058]

theorem width_15059 : mW 15059 = 419069898152488 := by
  have hu : mW 15059 ≤ 419069898152488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15059 ≤ 419069898152487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15059 : RowArithmetic 15059 (547156988139904163841/500000000000000000000000) (74764890110159434355911/125000000000000000000000) (6051291748772797/1000000000000000000000000) where
  r0 := (541135218731/1000000000000000000)
  k0 := (3477696383906717/1000000000000000000)
  k6 := (2789604134610711/250000000000000000)
  q := (173545383113466893519/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15059]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15059]

theorem width_15060 : mW 15060 = 419167306107692 := by
  have hu : mW 15060 ≤ 419167306107692 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15060 ≤ 419167306107691 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15060 : RowArithmetic 15060 (43771573774546755457/40000000000000000000000) (119621856143565490320887/200000000000000000000000) (302512405715243/50000000000000000000000) where
  r0 := (108216264339/200000000000000000)
  k0 := (3477523190416313/1000000000000000000)
  k6 := (2231609213387259/200000000000000000)
  q := (34710229039866619699/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15060]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15060]

theorem width_15061 : mW 15061 = 419264730234217 := by
  have hu : mW 15061 ≤ 419264730234217 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15061 ≤ 419264730234216 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15061 : RowArithmetic 15061 (547132358956382123159/500000000000000000000000) (598099441841889948047783/1000000000000000000000000) (756150591431049/125000000000000000000000) where
  r0 := (270513716803/500000000000000000)
  k0 := (217334376065773/62500000000000000)
  k6 := (557883781616373/50000000000000000)
  q := (34711381418779633467/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15061]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15061]

theorem width_15062 : mW 15062 = 419362170533675 := by
  have hu : mW 15062 ≤ 419362170533675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15062 ≤ 419362170533674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15062 : RowArithmetic 15062 (273560024231376573793/250000000000000000000000) (299044802126596864909347/500000000000000000000000) (6048161600125487/1000000000000000000000000) where
  r0 := (540973554461/1000000000000000000)
  k0 := (3477176863808247/1000000000000000000)
  k6 := (1394663154326277/125000000000000000)
  q := (173562668797181152357/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15062]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15062]

theorem width_15063 : mW 15063 = 419459627007675 := by
  have hu : mW 15063 ≤ 419459627007675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15063 ≤ 419459627007674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15063 : RowArithmetic 15063 (1094215481400308658463/1000000000000000000000000) (4784638143611756456143/8000000000000000000000) (6047118720258317/1000000000000000000000000) where
  r0 := (540919684259/1000000000000000000)
  k0 := (3477003730683741/1000000000000000000)
  k6 := (278923371844461/25000000000000000)
  q := (86784215154600551357/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15063]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15063]

theorem width_15064 : mW 15064 = 419557099657829 := by
  have hu : mW 15064 ≤ 419557099657829 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15064 ≤ 419557099657828 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15064 : RowArithmetic 15064 (1094190871335584404233/1000000000000000000000000) (598069932936448408216809/1000000000000000000000000) (6046076091769037/1000000000000000000000000) where
  r0 := (135216455749/250000000000000000)
  k0 := (3476830617669/1000000000000000)
  k6 := (11156564549826009/1000000000000000000)
  q := (173574191629977064399/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15064]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15064]

theorem width_15065 : mW 15065 = 419654588485748 := by
  have hu : mW 15065 ≤ 419654588485748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15065 ≤ 419654588485747 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15065 : RowArithmetic 15065 (1094166266729747572827/1000000000000000000000000) (598060099207861170896507/1000000000000000000000000) (755629214322481/125000000000000000000000) where
  r0 := (540811970671/1000000000000000000)
  k0 := (695331504952763/200000000000000000)
  k6 := (2231238852549361/200000000000000000)
  q := (34715990551905616049/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15065]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15065]

theorem width_15066 : mW 15066 = 419752093493043 := by
  have hu : mW 15066 ≤ 419752093493043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15066 ≤ 419752093493042 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15066 : RowArithmetic 15066 (1094141667581212794073/1000000000000000000000000) (598050266765438951077121/1000000000000000000000000) (6043991588612981/1000000000000000000000000) where
  r0 := (540758127283/1000000000000000000)
  k0 := (869121112991993/250000000000000000)
  k6 := (11155824012534707/1000000000000000000)
  q := (43396428424468297481/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15066]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15066]

theorem width_15067 : mW 15067 = 419849614681324 := by
  have hu : mW 15067 ≤ 419849614681324 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15067 ≤ 419849614681323 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15067 : RowArithmetic 15067 (21882341477767913373/20000000000000000000000) (59804043560891280931153/100000000000000000000000) (755368714223839/125000000000000000000000) where
  r0 := (135176073207/250000000000000000)
  k0 := (3476311399271619/1000000000000000000)
  k6 := (11155453799183599/1000000000000000000)
  q := (43397868611257857487/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15067]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15067]

theorem width_15068 : mW 15068 = 419947152052202 := by
  have hu : mW 15068 ≤ 419947152052202 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15068 ≤ 419947152052201 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15068 : RowArithmetic 15068 (1094092485649712004053/1000000000000000000000000) (299015302869007011607071/500000000000000000000000) (6041908090035333/1000000000000000000000000) where
  r0 := (67581308413/125000000000000000)
  k0 := (3476138366671327/1000000000000000000)
  k6 := (2231016724537473/200000000000000000)
  q := (21699654375127729209/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15068]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15068]

theorem width_15069 : mW 15069 = 420044705607290 := by
  have hu : mW 15069 ≤ 420044705607290 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15069 ≤ 420044705607289 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15069 : RowArithmetic 15069 (547033951431788716841/500000000000000000000000) (299010388576236900658497/500000000000000000000000) (377554169829321/62500000000000000000000) where
  r0 := (540596650711/1000000000000000000)
  k0 := (1737982677085049/500000000000000000)
  k6 := (11154713483039891/1000000000000000000)
  q := (173602995365863431291/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15069]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15069]

theorem width_15070 : mW 15070 = 420142275348197 := by
  have hu : mW 15070 ≤ 420142275348197 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15070 ≤ 420142275348196 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15070 : RowArithmetic 15070 (547021662764204852663/500000000000000000000000) (299005474926011786822819/500000000000000000000000) (6039825595414501/1000000000000000000000000) where
  r0 := (108108568609/200000000000000000)
  k0 := (434474045219759/125000000000000000)
  k6 := (11154343380235063/1000000000000000000)
  q := (86804377769787624923/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15070]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15070]

theorem width_15071 : mW 15071 = 420239861276536 := by
  have hu : mW 15071 ≤ 420239861276536 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15071 ≤ 420239861276535 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15071 : RowArithmetic 15071 (547009376821312814693/500000000000000000000000) (149500280959098679330463/250000000000000000000000) (3019392362196891/500000000000000000000000) where
  r0 := (108097808861/200000000000000000)
  k0 := (3475619389435033/1000000000000000000)
  k6 := (1115397331426677/100000000000000000)
  q := (86807257761088156609/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15071]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15071]

theorem width_15072 : mW 15072 = 420337463393916 := by
  have hu : mW 15072 ≤ 420337463393916 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15072 ≤ 420337463393915 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15072 : RowArithmetic 15072 (68374636700290258057/62500000000000000000000) (23919651964212751641073/40000000000000000000000) (3018872052064709/500000000000000000000000) where
  r0 := (67554406811/125000000000000000)
  k0 := (108607701162323/31250000000000000)
  k6 := (5576801642564451/500000000000000000)
  q := (86810137656842821067/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15072]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15072]

theorem width_15073 : mW 15073 = 420435081701950 := by
  have hu : mW 15073 ≤ 420435081701950 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15073 ≤ 420435081701949 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15073 : RowArithmetic 15073 (546984813106441595089/500000000000000000000000) (597981475658527324288671/1000000000000000000000000) (377293983408989/62500000000000000000000) where
  r0 := (540381473593/1000000000000000000)
  k0 := (1737636752517881/500000000000000000)
  k6 := (11153233292815349/1000000000000000000)
  q := (21703254364265281771/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15073]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15073]

theorem width_15074 : mW 15074 = 420532716202250 := by
  have hu : mW 15074 ≤ 420532716202250 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15074 ≤ 420532716202249 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15074 : RowArithmetic 15074 (218789014133152353697/200000000000000000000000) (149492913373937995223943/250000000000000000000000) (6035663615559457/1000000000000000000000000) where
  r0 := (540327701617/1000000000000000000)
  k0 := (434387574119083/125000000000000000)
  k6 := (2230572667464001/200000000000000000)
  q := (21703974290438145467/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15074]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15074]

theorem width_15075 : mW 15075 = 420630366896425 := by
  have hu : mW 15075 ≤ 420630366896425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15075 ≤ 420630366896424 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15075 : RowArithmetic 15075 (546960260280850274047/500000000000000000000000) (597961832616724587081443/1000000000000000000000000) (6034623747098847/1000000000000000000000000) where
  r0 := (270136969279/500000000000000000)
  k0 := (868731925235401/250000000000000000)
  k6 := (2788123354659191/250000000000000000)
  q := (21704694192731672763/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15075]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15075]

theorem width_15076 : mW 15076 = 420728033786089 := by
  have hu : mW 15076 ≤ 420728033786089 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15076 ≤ 420728033786088 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15076 : RowArithmetic 15076 (218779195179823779417/200000000000000000000000) (597952013021176873390111/1000000000000000000000000) (6033584129084483/1000000000000000000000000) where
  r0 := (270110092207/500000000000000000)
  k0 := (3474754828999149/1000000000000000000)
  k6 := (69700772104747/6250000000000000)
  q := (173643312569185917383/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15076]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15076]

theorem width_15077 : mW 15077 = 420825716872851 := by
  have hu : mW 15077 ≤ 420825716872851 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15077 ≤ 420825716872850 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15077 : RowArithmetic 15077 (1093871436676438672603/1000000000000000000000000) (4671423396162818547629/7812500000000000000000) (1508136190359739/250000000000000000000000) where
  r0 := (33760402449/62500000000000000)
  k0 := (868645494281269/250000000000000000)
  k6 := (2787938422920543/250000000000000000)
  q := (173649071405521774533/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15077]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15077]

theorem width_15078 : mW 15078 = 420923416158325 := by
  have hu : mW 15078 ≤ 420923416158325 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15078 ≤ 420923416158324 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15078 : RowArithmetic 15078 (4272839464422189127/3906250000000000000000) (597932377679448275165537/1000000000000000000000000) (1206301128816963/200000000000000000000000) where
  r0 := (33757043929/62500000000000000)
  k0 := (868602286327379/250000000000000000)
  k6 := (11151383883398617/1000000000000000000)
  q := (86827415025439977681/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15078]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15078]

theorem width_15079 : mW 15079 = 421021131644121 := by
  have hu : mW 15079 ≤ 421021131644121 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15079 ≤ 421021131644120 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15079 : RowArithmetic 15079 (1093822374544466777823/1000000000000000000000000) (597922561932731371565901/1000000000000000000000000) (753808347118087/125000000000000000000000) where
  r0 := (270029487727/500000000000000000)
  k0 := (3474236333555463/1000000000000000000)
  k6 := (2230202822380551/200000000000000000)
  q := (173660588505279458529/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15079]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15079]

theorem width_15080 : mW 15080 = 421118863331852 := by
  have hu : mW 15080 ≤ 421118863331852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15080 ≤ 421118863331851 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15080 : RowArithmetic 15080 (68362365727001240703/62500000000000000000000) (597912747468422244222079/1000000000000000000000000) (6029428159941223/1000000000000000000000000) where
  r0 := (10800105139/20000000000000000)
  k0 := (1737031770926521/500000000000000000)
  k6 := (11150644377188487/1000000000000000000)
  q := (173666346768739279541/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15080]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15080]

theorem width_15081 : mW 15081 = 421216611223128 := by
  have hu : mW 15081 ≤ 421216611223128 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15081 ≤ 421216611223127 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15081 : RowArithmetic 15081 (1093773334153163456721/1000000000000000000000000) (597902934286253083068939/1000000000000000000000000) (1507097448249273/250000000000000000000000) where
  r0 := (67493943419/125000000000000000)
  k0 := (3473890770205247/1000000000000000000)
  k6 := (2230054935849943/200000000000000000)
  q := (173672104841278410759/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15081]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15081]

theorem width_15082 : mW 15082 = 421314375319562 := by
  have hu : mW 15082 ≤ 421314375319562 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15082 ≤ 421314375319561 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15082 : RowArithmetic 15082 (1093748822106320860199/1000000000000000000000000) (597893122385956151771539/1000000000000000000000000) (1205470335206997/200000000000000000000000) where
  r0 := (4217951927/7812500000000000)
  k0 := (3473718018602201/1000000000000000000)
  k6 := (1393738127260043/125000000000000000)
  q := (173677862722915841391/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15082]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15082]

theorem width_15083 : mW 15083 = 421412155622766 := by
  have hu : mW 15083 ≤ 421412155622766 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15083 ≤ 421412155622765 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15083 : RowArithmetic 15083 (1093724315489916292803/1000000000000000000000000) (298941655883631905796447/500000000000000000000000) (6026313808977631/1000000000000000000000000) where
  r0 := (539844154861/1000000000000000000)
  k0 := (3473545287043679/1000000000000000000)
  k6 := (278738384841857/25000000000000000)
  q := (173683620413670557503/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15083]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15083]

theorem width_15084 : mW 15084 = 421509952134351 := by
  have hu : mW 15084 ≤ 421509952134351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15084 ≤ 421509952134350 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15084 : RowArithmetic 15084 (109369981430237494981/100000000000000000000000) (74734187803738564573507/125000000000000000000000) (6025276191747801/1000000000000000000000000) where
  r0 := (134947617991/250000000000000000)
  k0 := (1736686287761509/500000000000000000)
  k6 := (2787291451506357/250000000000000000)
  q := (17368937791356154201/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15084]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15084]

theorem width_15085 : mW 15085 = 421607764855930 := by
  have hu : mW 15085 ≤ 421607764855930 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15085 ≤ 421607764855929 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15085 : RowArithmetic 15085 (109367531854212185259/100000000000000000000000) (23914547774944909372791/40000000000000000000000) (1506059706067067/250000000000000000000000) where
  r0 := (134934199491/250000000000000000)
  k0 := (3473199884039991/1000000000000000000)
  k6 := (11148796255127697/1000000000000000000)
  q := (173695135222607774681/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15085]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15085]

theorem width_15086 : mW 15086 = 421705593789114 := by
  have hu : mW 15086 ≤ 421705593789114 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15086 ≤ 421705593789113 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15086 : RowArithmetic 15086 (109365082820758336527/100000000000000000000000) (74731735949767389212691/125000000000000000000000) (6023201706461863/1000000000000000000000000) where
  r0 := (539683132859/1000000000000000000)
  k0 := (69460544251823/20000000000000000)
  k6 := (11148426740974997/1000000000000000000)
  q := (173700892340828232143/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15086]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15086]

theorem width_15087 : mW 15087 = 421803438935516 := by
  have hu : mW 15087 ≤ 421803438935516 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15087 ≤ 421803438935515 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15087 : RowArithmetic 15087 (546813171648592839049/500000000000000000000000) (298922041051595136428359/500000000000000000000000) (6022164838251419/1000000000000000000000000) where
  r0 := (269814738323/500000000000000000)
  k0 := (434106820146229/125000000000000000)
  k6 := (11148057263561239/1000000000000000000)
  q := (86853324634120943937/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15087]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15087]

theorem width_15088 : mW 15088 = 421901300296747 := by
  have hu : mW 15088 ≤ 421901300296747 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15088 ≤ 421901300296746 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15088 : RowArithmetic 15088 (68350116488084770183/62500000000000000000000) (597834277888508940371313/1000000000000000000000000) (1505282054889957/250000000000000000000000) where
  r0 := (539575829323/1000000000000000000)
  k0 := (1736340964886293/500000000000000000)
  k6 := (2229537564576067/200000000000000000)
  q := (43428101501216928053/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15088]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15088]

theorem width_15089 : mW 15089 = 421999177874420 := by
  have hu : mW 15089 ≤ 421999177874420 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15089 ≤ 421999177874419 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15089 : RowArithmetic 15089 (1093577389742522657761/1000000000000000000000000) (74728059369228496669139/125000000000000000000000) (3010045925154991/500000000000000000000000) where
  r0 := (539522190889/1000000000000000000)
  k0 := (1736254659199591/500000000000000000)
  k6 := (11147318418926199/1000000000000000000)
  q := (173718162550724672349/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15089]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15089]

theorem width_15090 : mW 15090 = 422097071670147 := by
  have hu : mW 15090 ≤ 422097071670147 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15090 ≤ 422097071670146 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15090 : RowArithmetic 15090 (1093552921095113002777/1000000000000000000000000) (298907336649440113659191/500000000000000000000000) (3009527865212409/500000000000000000000000) where
  r0 := (539468561341/1000000000000000000)
  k0 := (3472336727042951/1000000000000000000)
  k6 := (5573474525846373/500000000000000000)
  q := (86861959452915866167/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15090]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15090]

theorem width_15091 : mW 15091 = 422194981685540 := by
  have hu : mW 15091 ≤ 422194981685540 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15091 ≤ 422194981685539 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15091 : RowArithmetic 15091 (273382114466389065297/250000000000000000000000) (149451218230849676328083/250000000000000000000000) (6018019859827301/1000000000000000000000000) where
  r0 := (539414940677/1000000000000000000)
  k0 := (3472164155700441/1000000000000000000)
  k6 := (11146579721173893/1000000000000000000)
  q := (86864837535103926539/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15091]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15091]

theorem width_15092 : mW 15092 = 422292907922212 := by
  have hu : mW 15092 ≤ 422292907922212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15092 ≤ 422292907922211 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15092 : RowArithmetic 15092 (273376000013070385241/250000000000000000000000) (149448768456779104453857/250000000000000000000000) (3008492119220207/500000000000000000000000) where
  r0 := (2106880191/3906250000000000)
  k0 := (3471991604371417/1000000000000000000)
  k6 := (11146210427363559/1000000000000000000)
  q := (86867715521935996173/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15092]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15092]

theorem width_15093 : mW 15093 = 422390850381774 := by
  have hu : mW 15093 ≤ 422390850381774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15093 ≤ 422390850381773 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15093 : RowArithmetic 15093 (136684943456714911103/125000000000000000000000) (597785276009766537444883/1000000000000000000000000) (6015948866187197/1000000000000000000000000) where
  r0 := (269653862997/500000000000000000)
  k0 := (867954768261497/250000000000000000)
  k6 := (5572920585127831/500000000000000000)
  q := (339338255521177939/1953125000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15093]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15093]

theorem width_15094 : mW 15094 = 422488809065840 := by
  have hu : mW 15094 ≤ 422488809065840 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15094 ≤ 422488809065839 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15094 : RowArithmetic 15094 (546727550334149699997/500000000000000000000000) (59777547947108222052849/100000000000000000000000) (3007456871495339/500000000000000000000000) where
  r0 := (539254131971/1000000000000000000)
  k0 := (3471646561727137/1000000000000000000)
  k6 := (2786367987461031/250000000000000000)
  q := (173746942419140141829/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15094]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15094]

theorem width_15095 : mW 15095 = 422586783976022 := by
  have hu : mW 15095 ≤ 422586783976022 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15095 ≤ 422586783976021 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15095 : RowArithmetic 15095 (109343065909445310789/100000000000000000000000) (298882842105398382524221/500000000000000000000000) (3006939434386971/500000000000000000000000) where
  r0 := (539200546823/1000000000000000000)
  k0 := (347147407040497/100000000000000000)
  k6 := (5572551383061433/500000000000000000)
  q := (173752697820782051879/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15095]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15095]

theorem width_15096 : mW 15096 = 422684775113932 := by
  have hu : mW 15096 ≤ 422684775113932 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15096 ≤ 422684775113931 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15096 : RowArithmetic 15096 (546703111465306113781/500000000000000000000000) (597755890228643482156471/1000000000000000000000000) (751605530432513/125000000000000000000000) where
  r0 := (10782939411/20000000000000000)
  k0 := (3471301599082469/1000000000000000000)
  k6 := (11144733619085813/1000000000000000000)
  q := (173758453031787780129/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15096]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15096]

theorem width_15097 : mW 15097 = 422782782481183 := by
  have hu : mW 15097 ≤ 422782782481183 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15097 ≤ 422782782481182 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15097 : RowArithmetic 15097 (1093381792175208778153/1000000000000000000000000) (119549219504871172275389/200000000000000000000000) (751476233371537/125000000000000000000000) where
  r0 := (134773350787/250000000000000000)
  k0 := (694225829549947/200000000000000000)
  k6 := (1114436450872689/100000000000000000)
  q := (43441052013044067163/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15097]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15097]

theorem width_15098 : mW 15098 = 422880806079388 := by
  have hu : mW 15098 ≤ 422880806079388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15098 ≤ 422880806079387 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15098 : RowArithmetic 15098 (218671473365335072093/200000000000000000000000) (597736306097667339135391/1000000000000000000000000) (3005387869616839/500000000000000000000000) where
  r0 := (67379980577/125000000000000000)
  k0 := (347095671640653/100000000000000000)
  k6 := (1392999429380003/125000000000000000)
  q := (2715155670030725881/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15098]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15098]

theorem width_15099 : mW 15099 = 422978845910159 := by
  have hu : mW 15099 ≤ 422978845910159 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15099 ≤ 422978845910158 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15099 : RowArithmetic 15099 (1093332946883445533651/1000000000000000000000000) (298863257974155776887733/500000000000000000000000) (3004870930083727/500000000000000000000000) where
  r0 := (67373286869/125000000000000000)
  k0 := (1735392152524697/500000000000000000)
  k6 := (11143626398019141/1000000000000000000)
  q := (86887858760588639563/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15099]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15099]

theorem width_15100 : mW 15100 = 423076901975108 := by
  have hu : mW 15100 ≤ 423076901975108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15100 ≤ 423076901975107 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15100 : RowArithmetic 15100 (1093308532343953437389/1000000000000000000000000) (29885836353801106660107/50000000000000000000000) (3004354114848429/500000000000000000000000) where
  r0 := (269466377077/500000000000000000)
  k0 := (216913244604679/62500000000000000)
  k6 := (11143257397658173/1000000000000000000)
  q := (21722683996228458693/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15100]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15100]

theorem width_15101 : mW 15101 = 423174974275850 := by
  have hu : mW 15101 ≤ 423174974275850 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15101 ≤ 423174974275849 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15101 : RowArithmetic 15101 (1093284123206632661547/1000000000000000000000000) (149426734870133206570781/250000000000000000000000) (6007674847745113/1000000000000000000000000) where
  r0 := (538879222219/1000000000000000000)
  k0 := (3470439542276259/1000000000000000000)
  k6 := (1392861054243881/125000000000000000)
  q := (173787226227936557167/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15101]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15101]

theorem width_15102 : mW 15102 = 423273062813997 := by
  have hu : mW 15102 ≤ 423273062813997 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15102 ≤ 423273062813996 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15102 : RowArithmetic 15102 (218651943893983701463/200000000000000000000000) (597697153161577447932397/1000000000000000000000000) (6006641714235511/1000000000000000000000000) where
  r0 := (269412849573/500000000000000000)
  k0 := (433783398856667/125000000000000000)
  k6 := (11142519506891701/1000000000000000000)
  q := (86896490147761434197/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15102]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15102]

theorem width_15103 : mW 15103 = 423371167591161 := by
  have hu : mW 15103 ≤ 423371167591161 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15103 ≤ 423371167591160 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15103 : RowArithmetic 15103 (546617660566123427783/500000000000000000000000) (37355460507430615717497/62500000000000000000000) (6005608829091377/1000000000000000000000000) where
  r0 := (134693046233/250000000000000000)
  k0 := (3470094859399409/1000000000000000000)
  k6 := (11142150616474063/1000000000000000000)
  q := (173798734172605526489/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15103]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15103]

theorem width_15104 : mW 15104 = 423469288608955 := by
  have hu : mW 15104 ≤ 423469288608955 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15104 ≤ 423469288608954 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15104 : RowArithmetic 15104 (1093210928192053790339/1000000000000000000000000) (119535516870440805434139/200000000000000000000000) (6004576192236047/1000000000000000000000000) where
  r0 := (67339834947/125000000000000000)
  k0 := (3469922547914233/1000000000000000000)
  k6 := (11141781762692071/1000000000000000000)
  q := (173804487859203451583/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15104]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15104]

theorem width_15105 : mW 15105 = 423567425868993 := by
  have hu : mW 15105 ≤ 423567425868993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15105 ≤ 423567425868992 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15105 : RowArithmetic 15105 (273296635161943899819/250000000000000000000000) (59766780186125401822327/100000000000000000000000) (3001771901796439/500000000000000000000000) where
  r0 := (21546607323/40000000000000000)
  k0 := (1734875128195561/500000000000000000)
  k6 := (11141412945539661/1000000000000000000)
  q := (43452560338833890169/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15105]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15105]

theorem width_15106 : mW 15106 = 423665579372888 := by
  have hu : mW 15106 ≤ 423665579372888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15106 ≤ 423665579372887 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15106 : RowArithmetic 15106 (1093162158497849525993/1000000000000000000000000) (597658020645773919360271/1000000000000000000000000) (3001255831542633/500000000000000000000000) where
  r0 := (538611695427/1000000000000000000)
  k0 := (1734788992413303/500000000000000000)
  k6 := (1114104416501077/100000000000000000)
  q := (86907997330510383819/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15106]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15106]

theorem width_15107 : mW 15107 = 423763749122252 := by
  have hu : mW 15107 ≤ 423763749122252 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15107 ≤ 423763749122251 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15107 : RowArithmetic 15107 (43725511269628550763/40000000000000000000000) (597648240705497926878733/1000000000000000000000000) (6001479770636653/1000000000000000000000000) where
  r0 := (538558216631/1000000000000000000)
  k0 := (3469405733220439/1000000000000000000)
  k6 := (11140675421099337/1000000000000000000)
  q := (21727718472034747901/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15107]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15107]

theorem width_15108 : mW 15108 = 423861935118700 := by
  have hu : mW 15108 ≤ 423861935118700 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15108 ≤ 423861935118699 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15108 : RowArithmetic 15108 (1093113410374805978397/1000000000000000000000000) (597638462040160279622907/1000000000000000000000000) (6000448126170469/1000000000000000000000000) where
  r0 := (134626186671/250000000000000000)
  k0 := (346923350156593/100000000000000000)
  k6 := (1392538339224913/125000000000000000)
  q := (34765500140225222999/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15108]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15108]

theorem width_15109 : mW 15109 = 423960137363843 := by
  have hu : mW 15109 ≤ 423960137363843 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15109 ≤ 423960137363842 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15109 : RowArithmetic 15109 (1093089044398565885693/1000000000000000000000000) (149407171162373840936661/250000000000000000000000) (5999416729610229/1000000000000000000000000) where
  r0 := (107690257117/200000000000000000)
  k0 := (3469061289862829/1000000000000000000)
  k6 := (2784984510776153/250000000000000000)
  q := (173833253435584067481/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15109]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15109]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15035 then ⟨(1094906785975375015383/1000000000000000000000000), (59835567175862463992233/100000000000000000000000), (3038207331230857/500000000000000000000000)⟩ else
  if n = 15036 then ⟨(273720505603958246093/250000000000000000000000), (299172900306972058214879/500000000000000000000000), (1518841241469077/250000000000000000000000)⟩ else
  if n = 15037 then ⟨(547428632179899885999/500000000000000000000000), (37395995672703727566831/62500000000000000000000), (6074315522780469/1000000000000000000000000)⟩ else
  if n = 15038 then ⟨(547416255902837281831/500000000000000000000000), (119665212441260027117931/200000000000000000000000), (3036633166547811/500000000000000000000000)⟩ else
  if n = 15039 then ⟨(1094807764751856368531/1000000000000000000000000), (598316194942794489891317/1000000000000000000000000), (3036108698371597/500000000000000000000000)⟩ else
  if n = 15040 then ⟨(1094783023196744792071/1000000000000000000000000), (299153164486235886423889/500000000000000000000000), (6071168713644641/1000000000000000000000000)⟩ else
  if n = 15041 then ⟨(547379143569370017881/500000000000000000000000), (598296464295061067199317/1000000000000000000000000), (6070120283721451/1000000000000000000000000)⟩ else
  if n = 15042 then ⟨(1094733556576243667531/1000000000000000000000000), (119657320182058324287339/200000000000000000000000), (6069072106895171/1000000000000000000000000)⟩ else
  if n = 15043 then ⟨(1094708831507656693911/1000000000000000000000000), (119655347763578523911567/200000000000000000000000), (1213604836617467/200000000000000000000000)⟩ else
  if n = 15044 then ⟨(218936822386276220449/200000000000000000000000), (11965337560351869142453/20000000000000000000000), (3033488256109761/500000000000000000000000)⟩ else
  if n = 15045 then ⟨(1094659397845819859661/1000000000000000000000000), (598257018509123540415493/1000000000000000000000000), (1516482273553339/250000000000000000000000)⟩ else
  if n = 15046 then ⟨(273658672312343939433/250000000000000000000000), (598247160292212345500239/1000000000000000000000000), (6064881928990463/1000000000000000000000000)⟩ else
  if n = 15047 then ⟨(1094609986140453336777/1000000000000000000000000), (598237303366589496576979/1000000000000000000000000), (303191750823627/50000000000000000000000)⟩ else
  if n = 15048 then ⟨(43783411540698263061/40000000000000000000000), (149556861932996154907261/250000000000000000000000), (242511534263251/40000000000000000000000)⟩ else
  if n = 15049 then ⟨(547280298189395025509/500000000000000000000000), (299108796694063714134661/500000000000000000000000), (1212348389847677/200000000000000000000000)⟩ else
  if n = 15050 then ⟨(68408494357678755053/62500000000000000000000), (299103870167373868318499/500000000000000000000000), (3030347897182829/500000000000000000000000)⟩ else
  if n = 15051 then ⟨(1094511228548072042473/1000000000000000000000000), (37387368035723465590529/62500000000000000000000), (6059649891884859/1000000000000000000000000)⟩ else
  if n = 15052 then ⟨(1094486552852833058033/1000000000000000000000000), (598188038098340536678213/1000000000000000000000000), (94665691276841/15625000000000000000000)⟩ else
  if n = 15053 then ⟨(547230941317775037099/500000000000000000000000), (299089094457386524910083/500000000000000000000000), (6057558843786391/1000000000000000000000000)⟩ else
  if n = 15054 then ⟨(1094437217894631014109/1000000000000000000000000), (119633668204120605815561/200000000000000000000000), (3028256849006221/500000000000000000000000)⟩ else
  if n = 15055 then ⟨(218882511725696878583/200000000000000000000000), (37384905900972547109757/62500000000000000000000), (6055468804317891/1000000000000000000000000)⟩ else
  if n = 15056 then ⟨(1094387904835518934213/1000000000000000000000000), (14953716227484412041217/25000000000000000000000), (6054424162624667/1000000000000000000000000)⟩ else
  if n = 15057 then ⟨(218872651302828867353/200000000000000000000000), (5981388050717805150047/10000000000000000000000), (6053379772854743/1000000000000000000000000)⟩ else
  if n = 15058 then ⟨(273584653415692626877/250000000000000000000000), (119625792466500669369899/200000000000000000000000), (1513083908732527/250000000000000000000000)⟩ else
  if n = 15059 then ⟨(547156988139904163841/500000000000000000000000), (74764890110159434355911/125000000000000000000000), (6051291748772797/1000000000000000000000000)⟩ else
  if n = 15060 then ⟨(43771573774546755457/40000000000000000000000), (119621856143565490320887/200000000000000000000000), (302512405715243/50000000000000000000000)⟩ else
  if n = 15061 then ⟨(547132358956382123159/500000000000000000000000), (598099441841889948047783/1000000000000000000000000), (756150591431049/125000000000000000000000)⟩ else
  if n = 15062 then ⟨(273560024231376573793/250000000000000000000000), (299044802126596864909347/500000000000000000000000), (6048161600125487/1000000000000000000000000)⟩ else
  if n = 15063 then ⟨(1094215481400308658463/1000000000000000000000000), (4784638143611756456143/8000000000000000000000), (6047118720258317/1000000000000000000000000)⟩ else
  if n = 15064 then ⟨(1094190871335584404233/1000000000000000000000000), (598069932936448408216809/1000000000000000000000000), (6046076091769037/1000000000000000000000000)⟩ else
  if n = 15065 then ⟨(1094166266729747572827/1000000000000000000000000), (598060099207861170896507/1000000000000000000000000), (755629214322481/125000000000000000000000)⟩ else
  if n = 15066 then ⟨(1094141667581212794073/1000000000000000000000000), (598050266765438951077121/1000000000000000000000000), (6043991588612981/1000000000000000000000000)⟩ else
  if n = 15067 then ⟨(21882341477767913373/20000000000000000000000), (59804043560891280931153/100000000000000000000000), (755368714223839/125000000000000000000000)⟩ else
  if n = 15068 then ⟨(1094092485649712004053/1000000000000000000000000), (299015302869007011607071/500000000000000000000000), (6041908090035333/1000000000000000000000000)⟩ else
  if n = 15069 then ⟨(547033951431788716841/500000000000000000000000), (299010388576236900658497/500000000000000000000000), (377554169829321/62500000000000000000000)⟩ else
  if n = 15070 then ⟨(547021662764204852663/500000000000000000000000), (299005474926011786822819/500000000000000000000000), (6039825595414501/1000000000000000000000000)⟩ else
  if n = 15071 then ⟨(547009376821312814693/500000000000000000000000), (149500280959098679330463/250000000000000000000000), (3019392362196891/500000000000000000000000)⟩ else
  if n = 15072 then ⟨(68374636700290258057/62500000000000000000000), (23919651964212751641073/40000000000000000000000), (3018872052064709/500000000000000000000000)⟩ else
  if n = 15073 then ⟨(546984813106441595089/500000000000000000000000), (597981475658527324288671/1000000000000000000000000), (377293983408989/62500000000000000000000)⟩ else
  if n = 15074 then ⟨(218789014133152353697/200000000000000000000000), (149492913373937995223943/250000000000000000000000), (6035663615559457/1000000000000000000000000)⟩ else
  if n = 15075 then ⟨(546960260280850274047/500000000000000000000000), (597961832616724587081443/1000000000000000000000000), (6034623747098847/1000000000000000000000000)⟩ else
  if n = 15076 then ⟨(218779195179823779417/200000000000000000000000), (597952013021176873390111/1000000000000000000000000), (6033584129084483/1000000000000000000000000)⟩ else
  if n = 15077 then ⟨(1093871436676438672603/1000000000000000000000000), (4671423396162818547629/7812500000000000000000), (1508136190359739/250000000000000000000000)⟩ else
  if n = 15078 then ⟨(4272839464422189127/3906250000000000000000), (597932377679448275165537/1000000000000000000000000), (1206301128816963/200000000000000000000000)⟩ else
  if n = 15079 then ⟨(1093822374544466777823/1000000000000000000000000), (597922561932731371565901/1000000000000000000000000), (753808347118087/125000000000000000000000)⟩ else
  if n = 15080 then ⟨(68362365727001240703/62500000000000000000000), (597912747468422244222079/1000000000000000000000000), (6029428159941223/1000000000000000000000000)⟩ else
  if n = 15081 then ⟨(1093773334153163456721/1000000000000000000000000), (597902934286253083068939/1000000000000000000000000), (1507097448249273/250000000000000000000000)⟩ else
  if n = 15082 then ⟨(1093748822106320860199/1000000000000000000000000), (597893122385956151771539/1000000000000000000000000), (1205470335206997/200000000000000000000000)⟩ else
  if n = 15083 then ⟨(1093724315489916292803/1000000000000000000000000), (298941655883631905796447/500000000000000000000000), (6026313808977631/1000000000000000000000000)⟩ else
  if n = 15084 then ⟨(109369981430237494981/100000000000000000000000), (74734187803738564573507/125000000000000000000000), (6025276191747801/1000000000000000000000000)⟩ else
  if n = 15085 then ⟨(109367531854212185259/100000000000000000000000), (23914547774944909372791/40000000000000000000000), (1506059706067067/250000000000000000000000)⟩ else
  if n = 15086 then ⟨(109365082820758336527/100000000000000000000000), (74731735949767389212691/125000000000000000000000), (6023201706461863/1000000000000000000000000)⟩ else
  if n = 15087 then ⟨(546813171648592839049/500000000000000000000000), (298922041051595136428359/500000000000000000000000), (6022164838251419/1000000000000000000000000)⟩ else
  if n = 15088 then ⟨(68350116488084770183/62500000000000000000000), (597834277888508940371313/1000000000000000000000000), (1505282054889957/250000000000000000000000)⟩ else
  if n = 15089 then ⟨(1093577389742522657761/1000000000000000000000000), (74728059369228496669139/125000000000000000000000), (3010045925154991/500000000000000000000000)⟩ else
  if n = 15090 then ⟨(1093552921095113002777/1000000000000000000000000), (298907336649440113659191/500000000000000000000000), (3009527865212409/500000000000000000000000)⟩ else
  if n = 15091 then ⟨(273382114466389065297/250000000000000000000000), (149451218230849676328083/250000000000000000000000), (6018019859827301/1000000000000000000000000)⟩ else
  if n = 15092 then ⟨(273376000013070385241/250000000000000000000000), (149448768456779104453857/250000000000000000000000), (3008492119220207/500000000000000000000000)⟩ else
  if n = 15093 then ⟨(136684943456714911103/125000000000000000000000), (597785276009766537444883/1000000000000000000000000), (6015948866187197/1000000000000000000000000)⟩ else
  if n = 15094 then ⟨(546727550334149699997/500000000000000000000000), (59777547947108222052849/100000000000000000000000), (3007456871495339/500000000000000000000000)⟩ else
  if n = 15095 then ⟨(109343065909445310789/100000000000000000000000), (298882842105398382524221/500000000000000000000000), (3006939434386971/500000000000000000000000)⟩ else
  if n = 15096 then ⟨(546703111465306113781/500000000000000000000000), (597755890228643482156471/1000000000000000000000000), (751605530432513/125000000000000000000000)⟩ else
  if n = 15097 then ⟨(1093381792175208778153/1000000000000000000000000), (119549219504871172275389/200000000000000000000000), (751476233371537/125000000000000000000000)⟩ else
  if n = 15098 then ⟨(218671473365335072093/200000000000000000000000), (597736306097667339135391/1000000000000000000000000), (3005387869616839/500000000000000000000000)⟩ else
  if n = 15099 then ⟨(1093332946883445533651/1000000000000000000000000), (298863257974155776887733/500000000000000000000000), (3004870930083727/500000000000000000000000)⟩ else
  if n = 15100 then ⟨(1093308532343953437389/1000000000000000000000000), (29885836353801106660107/50000000000000000000000), (3004354114848429/500000000000000000000000)⟩ else
  if n = 15101 then ⟨(1093284123206632661547/1000000000000000000000000), (149426734870133206570781/250000000000000000000000), (6007674847745113/1000000000000000000000000)⟩ else
  if n = 15102 then ⟨(218651943893983701463/200000000000000000000000), (597697153161577447932397/1000000000000000000000000), (6006641714235511/1000000000000000000000000)⟩ else
  if n = 15103 then ⟨(546617660566123427783/500000000000000000000000), (37355460507430615717497/62500000000000000000000), (6005608829091377/1000000000000000000000000)⟩ else
  if n = 15104 then ⟨(1093210928192053790339/1000000000000000000000000), (119535516870440805434139/200000000000000000000000), (6004576192236047/1000000000000000000000000)⟩ else
  if n = 15105 then ⟨(273296635161943899819/250000000000000000000000), (59766780186125401822327/100000000000000000000000), (3001771901796439/500000000000000000000000)⟩ else
  if n = 15106 then ⟨(1093162158497849525993/1000000000000000000000000), (597658020645773919360271/1000000000000000000000000), (3001255831542633/500000000000000000000000)⟩ else
  if n = 15107 then ⟨(43725511269628550763/40000000000000000000000), (597648240705497926878733/1000000000000000000000000), (6001479770636653/1000000000000000000000000)⟩ else
  if n = 15108 then ⟨(1093113410374805978397/1000000000000000000000000), (597638462040160279622907/1000000000000000000000000), (6000448126170469/1000000000000000000000000)⟩ else
  ⟨(1093089044398565885693/1000000000000000000000000), (149407171162373840936661/250000000000000000000000), (5999416729610229/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15035 ≤ n) (hb : n ≤ 15109) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15035
  · exact row_15036
  · exact row_15037
  · exact row_15038
  · exact row_15039
  · exact row_15040
  · exact row_15041
  · exact row_15042
  · exact row_15043
  · exact row_15044
  · exact row_15045
  · exact row_15046
  · exact row_15047
  · exact row_15048
  · exact row_15049
  · exact row_15050
  · exact row_15051
  · exact row_15052
  · exact row_15053
  · exact row_15054
  · exact row_15055
  · exact row_15056
  · exact row_15057
  · exact row_15058
  · exact row_15059
  · exact row_15060
  · exact row_15061
  · exact row_15062
  · exact row_15063
  · exact row_15064
  · exact row_15065
  · exact row_15066
  · exact row_15067
  · exact row_15068
  · exact row_15069
  · exact row_15070
  · exact row_15071
  · exact row_15072
  · exact row_15073
  · exact row_15074
  · exact row_15075
  · exact row_15076
  · exact row_15077
  · exact row_15078
  · exact row_15079
  · exact row_15080
  · exact row_15081
  · exact row_15082
  · exact row_15083
  · exact row_15084
  · exact row_15085
  · exact row_15086
  · exact row_15087
  · exact row_15088
  · exact row_15089
  · exact row_15090
  · exact row_15091
  · exact row_15092
  · exact row_15093
  · exact row_15094
  · exact row_15095
  · exact row_15096
  · exact row_15097
  · exact row_15098
  · exact row_15099
  · exact row_15100
  · exact row_15101
  · exact row_15102
  · exact row_15103
  · exact row_15104
  · exact row_15105
  · exact row_15106
  · exact row_15107
  · exact row_15108
  · exact row_15109

end BstLean.Part271.R3.Rows15035
