import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14476–14550. -/
namespace BstLean.Part271.R3.Rows14476
open Real BstLean.Part130 BstLean.Part227

theorem width_14476 : mW 14476 = 364980793067181 := by
  have hu : mW 14476 ≤ 364980793067181 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14476 ≤ 364980793067180 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14476 : RowArithmetic 14476 (277415095617695328981/250000000000000000000000) (604084448012335624369593/1000000000000000000000000) (6705300470686649/1000000000000000000000000) where
  r0 := (574152338919/1000000000000000000)
  k0 := (3582220648541859/1000000000000000000)
  k6 := (177826456633561/15625000000000000)
  q := (170152872441225628579/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14476]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14476]

theorem width_14477 : mW 14477 = 365069045559972 := by
  have hu : mW 14477 ≤ 365069045559972 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14477 ≤ 365069045559971 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14477 : RowArithmetic 14477 (1109632273883784460411/1000000000000000000000000) (75509226085174469544169/125000000000000000000000) (6704095842983199/1000000000000000000000000) where
  r0 := (114818570103/200000000000000000)
  k0 := (3582035065296019/1000000000000000000)
  k6 := (1422562518709827/125000000000000000)
  q := (85079374703861099781/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14477]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14477]

theorem width_14478 : mW 14478 = 365157313294199 := by
  have hu : mW 14478 ≤ 365157313294199 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14478 ≤ 365157313294198 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14478 : RowArithmetic 14478 (1109604171793298928187/1000000000000000000000000) (30203158540455300565593/50000000000000000000000) (3351445758889623/500000000000000000000000) where
  r0 := (287016686191/500000000000000000)
  k0 := (1790924752239587/500000000000000000)
  k6 := (11380107115534737/1000000000000000000)
  q := (170164626171246296427/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14478]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14478]

theorem width_14479 : mW 14479 = 365245596271443 := by
  have hu : mW 14479 ≤ 365245596271443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14479 ≤ 365245596271442 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14479 : RowArithmetic 14479 (221915215239471662589/200000000000000000000000) (604052534395146865879417/1000000000000000000000000) (3350843747488617/500000000000000000000000) where
  r0 := (573973904519/1000000000000000000)
  k0 := (358166396609169/100000000000000000)
  k6 := (11379714122109237/1000000000000000000)
  q := (170170502731818947871/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14479]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14479]

theorem width_14480 : mW 14480 = 365333894493282 := by
  have hu : mW 14480 ≤ 365333894493282 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14480 ≤ 365333894493281 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14480 : RowArithmetic 14480 (1109547987093998413589/1000000000000000000000000) (12080837988783974602989/20000000000000000000000) (837560471809963/125000000000000000000000) where
  r0 := (573914446923/1000000000000000000)
  k0 := (895369612531923/250000000000000000)
  k6 := (2844830292348771/250000000000000000)
  q := (85088189544730589479/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14480]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14480]

theorem width_14481 : mW 14481 = 365422207961296 := by
  have hu : mW 14481 ≤ 365422207961296 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14481 ≤ 365422207961295 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14481 : RowArithmetic 14481 (1109519904481254826911/1000000000000000000000000) (604031265940942336517287/1000000000000000000000000) (16748200890473/2500000000000000000000) where
  r0 := (573854999591/1000000000000000000)
  k0 := (3581292956581303/1000000000000000000)
  k6 := (11378928257385251/1000000000000000000)
  q := (85091127622097005561/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14481]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14481]

theorem width_14482 : mW 14482 = 365510536677064 := by
  have hu : mW 14482 ≤ 365510536677064 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14482 ≤ 365510536677063 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14482 : RowArithmetic 14482 (277372957089291097747/250000000000000000000000) (75502579237507288346617/125000000000000000000000) (3349038620004161/500000000000000000000000) where
  r0 := (286897781261/500000000000000000)
  k0 := (447638435681611/125000000000000000)
  k6 := (1137853538607271/100000000000000000)
  q := (17018813119603846217/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14482]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14482]

theorem width_14483 : mW 14483 = 365598880642166 := by
  have hu : mW 14483 ≤ 365598880642166 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14483 ≤ 365598880642165 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14483 : RowArithmetic 14483 (554731879359882111497/500000000000000000000000) (604010003316227562776669/1000000000000000000000000) (1674218606459923/250000000000000000000000) where
  r0 := (17929254241/31250000000000000)
  k0 := (716184407346689/200000000000000000)
  k6 := (11378142555450437/1000000000000000000)
  q := (170194006945015546279/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14483]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14483]

theorem width_14484 : mW 14484 = 365687239858182 := by
  have hu : mW 14484 ≤ 365687239858182 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14484 ≤ 365687239858181 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14484 : RowArithmetic 14484 (1109435695567092200013/1000000000000000000000000) (120799874837826183745057/200000000000000000000000) (6695671913585971/1000000000000000000000000) where
  r0 := (573676719159/1000000000000000000)
  k0 := (716147322084043/200000000000000000)
  k6 := (11377749765511407/1000000000000000000)
  q := (85099941245573137/500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14484]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14484]

theorem width_14485 : mW 14485 = 365775614326690 := by
  have hu : mW 14485 ≤ 365775614326690 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14485 ≤ 365775614326689 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14485 : RowArithmetic 14485 (1109407638897187918733/1000000000000000000000000) (603988746518449436848637/1000000000000000000000000) (1338893940629979/200000000000000000000000) where
  r0 := (573617312861/1000000000000000000)
  k0 := (1790275603255219/500000000000000000)
  k6 := (11377357016248599/1000000000000000000)
  q := (34041151566890330451/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14485]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14485]

theorem width_14486 : mW 14486 = 365864004049270 := by
  have hu : mW 14486 ≤ 365864004049270 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14486 ≤ 365864004049269 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14486 : RowArithmetic 14486 (554689794354045386881/500000000000000000000000) (301989060151932085576943/500000000000000000000000) (1338653558886841/200000000000000000000000) where
  r0 := (114711583363/200000000000000000)
  k0 := (358036582499823/100000000000000000)
  k6 := (5688482153827497/500000000000000000)
  q := (170211632974952684343/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14486]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14486]

theorem width_14487 : mW 14487 = 365952409027502 := by
  have hu : mW 14487 ≤ 365952409027502 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14487 ≤ 365952409027501 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14487 : RowArithmetic 14487 (13866894312473011481/12500000000000000000000) (75495936943132044248727/125000000000000000000000) (83650827341771/12500000000000000000000) where
  r0 := (573498531019/1000000000000000000)
  k0 := (3580180465880827/1000000000000000000)
  k6 := (11376571639723573/1000000000000000000)
  q := (85108753956335184969/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14487]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14487]

theorem width_14488 : mW 14488 = 366040829262966 := by
  have hu : mW 14488 ≤ 366040829262966 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14488 ≤ 366040829262965 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14488 : RowArithmetic 14488 (1109323507764479264661/1000000000000000000000000) (30197843612085362159371/50000000000000000000000) (209089527555473/31250000000000000000000) where
  r0 := (57343915547/100000000000000000)
  k0 := (3579995129152343/1000000000000000000)
  k6 := (5688089506223659/500000000000000000)
  q := (170223382647625705089/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14488]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14488]

theorem width_14489 : mW 14489 = 366129264757242 := by
  have hu : mW 14489 ≤ 366129264757242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14489 ≤ 366129264757241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14489 : RowArithmetic 14489 (110929547700604748209/100000000000000000000000) (603946250393498244217531/1000000000000000000000000) (6689663877637433/1000000000000000000000000) where
  r0 := (286689895083/500000000000000000)
  k0 := (1789904907405007/500000000000000000)
  k6 := (710986651613701/62500000000000000)
  q := (170229257179839682223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14489]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14489]

theorem width_14490 : mW 14490 = 366217715511909 := by
  have hu : mW 14490 ≤ 366217715511909 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14490 ≤ 366217715511908 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14490 : RowArithmetic 14490 (554633726360294238631/500000000000000000000000) (603935630000110869197621/1000000000000000000000000) (6688463174831483/1000000000000000000000000) where
  r0 := (17916263597/31250000000000000)
  k0 := (3579624522847949/1000000000000000000)
  k6 := (2843848469958063/250000000000000000)
  q := (5319847859666665317/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14490]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14490]

theorem width_14491 : mW 14491 = 366306181528547 := by
  have hu : mW 14491 ≤ 366306181528547 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14491 ≤ 366306181528546 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14491 : RowArithmetic 14491 (44369577396245817371/40000000000000000000000) (301962505530613323116177/500000000000000000000000) (104488480832191/15625000000000000000000) where
  r0 := (286630545141/500000000000000000)
  k0 := (178971962663169/50000000000000000)
  k6 := (1421875171809927/125000000000000000)
  q := (170241005636127514037/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14491]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14491]

theorem width_14492 : mW 14492 = 366394662808737 := by
  have hu : mW 14492 ≤ 366394662808737 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14492 ≤ 366394662808736 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14492 : RowArithmetic 14492 (55460571178038090771/50000000000000000000000) (120782878715305460326547/200000000000000000000000) (1671515668206653/250000000000000000000000) where
  r0 := (286600877849/500000000000000000)
  k0 := (1789627003026769/500000000000000000)
  k6 := (5687304454876849/500000000000000000)
  q := (170246879560243335463/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14492]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14492]

theorem width_14493 : mW 14493 = 366483159354058 := by
  have hu : mW 14493 ≤ 366483159354058 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14493 ≤ 366483159354057 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14493 : RowArithmetic 14493 (1109183418682482797247/1000000000000000000000000) (9435996524151477089369/15625000000000000000000) (3342431436716839/500000000000000000000000) where
  r0 := (143285607837/250000000000000000)
  k0 := (3579068781209409/1000000000000000000)
  k6 := (1421777060706011/125000000000000000)
  q := (170252753281701732367/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14493]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14493]

theorem width_14494 : mW 14494 = 366571671166090 := by
  have hu : mW 14494 ≤ 366571671166090 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14494 ≤ 366571671166089 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14494 : RowArithmetic 14494 (554577710134676916677/500000000000000000000000) (603893162968410251650779/1000000000000000000000000) (1670915843746119/250000000000000000000000) where
  r0 := (57308311723/100000000000000000)
  k0 := (3578883578728219/1000000000000000000)
  k6 := (5686912051077791/500000000000000000)
  q := (85129313400261839537/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14494]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14494]

theorem width_14495 : mW 14495 = 366660198246413 := by
  have hu : mW 14495 ≤ 366660198246413 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14495 ≤ 366660198246412 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14495 : RowArithmetic 14495 (221825485663884226617/200000000000000000000000) (603882549844356456651857/1000000000000000000000000) (3341232088691049/500000000000000000000000) where
  r0 := (573023813343/1000000000000000000)
  k0 := (1789349199305159/500000000000000000)
  k6 := (11373431759269173/1000000000000000000)
  q := (42566125029182536573/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14495]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14495]

theorem width_14496 : mW 14496 = 366748740596608 := by
  have hu : mW 14496 ≤ 366748740596608 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14496 ≤ 366748740596607 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14496 : RowArithmetic 14496 (1109099442830731183229/1000000000000000000000000) (150967984543303784847731/250000000000000000000000) (6681265280529657/1000000000000000000000000) where
  r0 := (572964519683/1000000000000000000)
  k0 := (1789256620423343/500000000000000000)
  k6 := (568651972849093/50000000000000000)
  q := (17027037323034210111/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14496]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14496]

theorem width_14497 : mW 14497 = 366837298218254 := by
  have hu : mW 14497 ≤ 366837298218254 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14497 ≤ 366837298218253 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14497 : RowArithmetic 14497 (1109071463801332181791/1000000000000000000000000) (603861327954668485250067/1000000000000000000000000) (3340033342165171/500000000000000000000000) where
  r0 := (71613154531/125000000000000000)
  k0 := (894582026358637/250000000000000000)
  k6 := (142158089941083/12500000000000000)
  q := (170276246141380507003/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14497]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14497]

theorem width_14498 : mW 14498 = 366925871112933 := by
  have hu : mW 14498 ≤ 366925871112933 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14498 ≤ 366925871112932 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14498 : RowArithmetic 14498 (1109043491229271648009/1000000000000000000000000) (603850719188398746465483/1000000000000000000000000) (3339434194343663/500000000000000000000000) where
  r0 := (114569192607/200000000000000000)
  k0 := (894535748092001/250000000000000000)
  k6 := (11372254974176513/1000000000000000000)
  q := (21285264856233290479/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14498]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14498]

theorem width_14499 : mW 14499 = 367014459282224 := by
  have hu : mW 14499 ≤ 367014459282224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14499 ≤ 367014459282223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14499 : RowArithmetic 14499 (44360621004503971557/40000000000000000000000) (603840111874088210289259/1000000000000000000000000) (3338835196751937/500000000000000000000000) where
  r0 := (572786700043/1000000000000000000)
  k0 := (1788978950823699/500000000000000000)
  k6 := (11371862793644483/1000000000000000000)
  q := (170287991355820507841/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14499]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14499]

theorem width_14500 : mW 14500 = 367103062727707 := by
  have hu : mW 14500 ≤ 367103062727707 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14500 ≤ 367103062727706 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14500 : RowArithmetic 14500 (1108987565449365087521/1000000000000000000000000) (603829506011419379714901/1000000000000000000000000) (1669118174670819/250000000000000000000000) where
  r0 := (143181861817/250000000000000000)
  k0 := (1788886416631853/500000000000000000)
  k6 := (355358457927611/31250000000000000)
  q := (85146931829632005831/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14500]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14500]

theorem width_14501 : mW 14501 = 367191681450964 := by
  have hu : mW 14501 ≤ 367191681450964 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14501 ≤ 367191681450963 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14501 : RowArithmetic 14501 (1108959612237618826337/1000000000000000000000000) (60381890160007475480077/100000000000000000000000) (6675275304128819/1000000000000000000000000) where
  r0 := (143167051177/250000000000000000)
  k0 := (715517557442829/200000000000000000)
  k6 := (454843142171469/40000000000000000)
  q := (34059947152043556863/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14501]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14501]

theorem width_14502 : mW 14502 = 367280315453574 := by
  have hu : mW 14502 ≤ 367280315453574 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14502 ≤ 367280315453573 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14502 : RowArithmetic 14502 (554465832737706236431/500000000000000000000000) (966093277823579207983/1600000000000000000000) (6674078209743889/1000000000000000000000000) where
  r0 := (572608972361/1000000000000000000)
  k0 := (715480552699187/200000000000000000)
  k6 := (1137068649544701/100000000000000000)
  q := (21288200957337846401/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14502]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14502]

theorem width_14503 : mW 14503 = 367368964737118 := by
  have hu : mW 14503 ≤ 367368964737118 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14503 ≤ 367368964737117 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14503 : RowArithmetic 14503 (1108903725160797793391/1000000000000000000000000) (301898848565044389686269/500000000000000000000000) (6672881415431871/1000000000000000000000000) where
  r0 := (35784359389/62500000000000000)
  k0 := (3577217762103169/1000000000000000000)
  k6 := (1421286809644677/125000000000000000)
  q := (85155739677369957069/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14503]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14503]

theorem width_14504 : mW 14504 = 367457629303178 := by
  have hu : mW 14504 ≤ 367457629303178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14504 ≤ 367457629303177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14504 : RowArithmetic 14504 (277218947822956707739/250000000000000000000000) (603787097070812977677479/1000000000000000000000000) (1667921230274043/250000000000000000000000) where
  r0 := (286245269147/500000000000000000)
  k0 := (1788516391514969/500000000000000000)
  k6 := (11369902499410953/1000000000000000000)
  q := (42579337712087537823/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14504]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14504]

theorem width_14505 : mW 14505 = 367546309153332 := by
  have hu : mW 14505 ≤ 367546309153332 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14505 ≤ 367546309153331 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14505 : RowArithmetic 14505 (138605982983319285859/125000000000000000000000) (301888249230796231407651/500000000000000000000000) (6670488726640311/1000000000000000000000000) where
  r0 := (57243133657/100000000000000000)
  k0 := (3576847826276581/1000000000000000000)
  k6 := (1421188820275079/125000000000000000)
  q := (681292888558217669/4000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14505]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14505]

theorem width_14506 : mW 14506 = 367635004289163 := by
  have hu : mW 14506 ≤ 367635004289163 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14506 ≤ 367635004289162 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14506 : RowArithmetic 14506 (554409971441516616257/500000000000000000000000) (120753180260422051046747/200000000000000000000000) (3334646415983877/500000000000000000000000) where
  r0 := (572372145049/1000000000000000000)
  k0 := (894165722959297/250000000000000000)
  k6 := (11369118665519469/1000000000000000000)
  q := (170329093228373642981/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14506]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14506]

theorem width_14507 : mW 14507 = 367723714712250 := by
  have hu : mW 14507 ≤ 367723714712250 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14507 ≤ 367723714712249 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14507 : RowArithmetic 14507 (44351681133572775841/40000000000000000000000) (15093882639801236790899/25000000000000000000000) (6668097236982079/1000000000000000000000000) where
  r0 := (35769560233/62500000000000000)
  k0 := (715295595941169/200000000000000000)
  k6 := (11368726809360477/1000000000000000000)
  q := (21291870514353594481/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14507]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14507]

theorem width_14508 : mW 14508 = 367812440424176 := by
  have hu : mW 14508 ≤ 367812440424176 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14508 ≤ 367812440424175 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14508 : RowArithmetic 14508 (17324439378647927393/15625000000000000000000) (603744711331093282756441/1000000000000000000000000) (6666901941586831/1000000000000000000000000) where
  r0 := (114450758521/200000000000000000)
  k0 := (715258617975953/200000000000000000)
  k6 := (454733399748667/40000000000000000)
  q := (21292604349867584951/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14508]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14508]

theorem width_14509 : mW 14509 = 367901181426519 := by
  have hu : mW 14509 ≤ 367901181426519 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14509 ≤ 367901181426518 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14509 : RowArithmetic 14509 (1108736218563534809567/1000000000000000000000000) (18866691203716406707383/31250000000000000000000) (1666426736421421/250000000000000000000000) where
  r0 := (286097315839/500000000000000000)
  k0 := (894027055589039/250000000000000000)
  k6 := (5683971609290541/500000000000000000)
  q := (42586676320182583603/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14509]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14509]

theorem width_14510 : mW 14510 = 367989937720863 := by
  have hu : mW 14510 ≤ 367989937720863 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14510 ≤ 367989937720862 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14510 : RowArithmetic 14510 (554354161663788684037/500000000000000000000000) (150930881788807011087507/250000000000000000000000) (6664512249182241/1000000000000000000000000) where
  r0 := (572135480943/1000000000000000000)
  k0 := (3575923377125977/1000000000000000000)
  k6 := (11367551483946717/1000000000000000000)
  q := (21294071945027329601/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14510]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14510]

theorem width_14511 : mW 14511 = 368078709308786 := by
  have hu : mW 14511 ≤ 368078709308786 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14511 ≤ 368078709308785 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14511 : RowArithmetic 14511 (554340217261827117279/500000000000000000000000) (603712937239685827602391/1000000000000000000000000) (3331658925990127/500000000000000000000000) where
  r0 := (572076340399/1000000000000000000)
  k0 := (3575738554189561/1000000000000000000)
  k6 := (5683579894903301/500000000000000000)
  q := (170358445637426499737/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14511]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14511]

theorem width_14512 : mW 14512 = 368167496191872 := by
  have hu : mW 14512 ≤ 368167496191872 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14512 ≤ 368167496191871 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14512 : RowArithmetic 14512 (554326276074911256791/500000000000000000000000) (120740469754396394530917/200000000000000000000000) (1332424750796681/200000000000000000000000) where
  r0 := (572017210043/1000000000000000000)
  k0 := (3575553753540989/1000000000000000000)
  k6 := (11366768136153763/1000000000000000000)
  q := (170364315512374832539/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14512]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14512]

theorem width_14513 : mW 14513 = 368256298371699 := by
  have hu : mW 14513 ≤ 368256298371699 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14513 ≤ 368256298371698 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14513 : RowArithmetic 14513 (221724935240828581949/200000000000000000000000) (37730735109487511610709/62500000000000000000000) (6660929955095523/1000000000000000000000000) where
  r0 := (35747380617/62500000000000000)
  k0 := (3575368975174339/1000000000000000000)
  k6 := (1420797065372653/125000000000000000)
  q := (85185092592542270477/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14513]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14513]

theorem width_14514 : mW 14514 = 368345115849851 := by
  have hu : mW 14514 ≤ 368345115849851 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14514 ≤ 368345115849850 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14514 : RowArithmetic 14514 (1108596806684674027867/1000000000000000000000000) (603681176178824203483291/1000000000000000000000000) (6659736455220367/1000000000000000000000000) where
  r0 := (114379795977/200000000000000000)
  k0 := (3575184219089941/1000000000000000000)
  k6 := (11365984950282013/1000000000000000000)
  q := (170376054655576527117/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14514]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14514]

theorem width_14515 : mW 14515 = 368433948627907 := by
  have hu : mW 14515 ≤ 368433948627907 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14515 ≤ 368433948627906 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14515 : RowArithmetic 14515 (277142235897369398871/250000000000000000000000) (60367059205273787288143/100000000000000000000000) (266341730170473/40000000000000000000000) where
  r0 := (285919940039/500000000000000000)
  k0 := (3574999485278747/1000000000000000000)
  k6 := (5682796709024579/500000000000000000)
  q := (34076384784774337913/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14515]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14515]

theorem width_14516 : mW 14516 = 368522796707449 := by
  have hu : mW 14516 ≤ 368522796707449 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14516 ≤ 368522796707448 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14516 : RowArithmetic 14516 (554270543458307332469/500000000000000000000000) (60366000937322514889439/100000000000000000000000) (665735035212377/100000000000000000000000) where
  r0 := (11435615809/20000000000000000)
  k0 := (1787407386870541/500000000000000000)
  k6 := (11365201926275691/1000000000000000000)
  q := (34077558597998184647/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14516]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14516]

theorem width_14517 : mW 14517 = 368611660090059 := by
  have hu : mW 14517 ≤ 368611660090059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14517 ≤ 368611660090058 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14517 : RowArithmetic 14517 (69282077291509189849/62500000000000000000000) (301824714069985063743041/500000000000000000000000) (3328078874355057/500000000000000000000000) where
  r0 := (571721710997/1000000000000000000)
  k0 := (714926016893579/200000000000000000)
  k6 := (11364810474954643/1000000000000000000)
  q := (85196830926977559733/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14517]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14517]

theorem width_14518 : mW 14518 = 368700538777318 := by
  have hu : mW 14518 ≤ 368700538777318 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14518 ≤ 368700538777317 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14518 : RowArithmetic 14518 (1108485392830137737129/1000000000000000000000000) (301819424176328472832089/500000000000000000000000) (831870680490603/125000000000000000000000) where
  r0 := (285831320859/500000000000000000)
  k0 := (446805677182439/125000000000000000)
  k6 := (11364419064079049/1000000000000000000)
  q := (85199765257892582999/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14518]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14518]

theorem width_14519 : mW 14519 = 368789432770807 := by
  have hu : mW 14519 ≤ 368789432770807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14519 ≤ 368789432770806 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14519 : RowArithmetic 14519 (55422877770632526739/50000000000000000000000) (603628270010969835204361/1000000000000000000000000) (665377343767191/100000000000000000000000) where
  r0 := (571603582609/1000000000000000000)
  k0 := (893565193176719/250000000000000000)
  k6 := (11364027693641943/1000000000000000000)
  q := (5325168717984435843/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14519]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14519]

theorem width_14520 : mW 14520 = 368878342072108 := by
  have hu : mW 14520 ≤ 368878342072108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14520 ≤ 368878342072107 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14520 : RowArithmetic 14520 (55421486220487473777/50000000000000000000000) (603617693114593097570289/1000000000000000000000000) (1663145432463849/250000000000000000000000) where
  r0 := (571544533669/1000000000000000000)
  k0 := (357407615021031/100000000000000000)
  k6 := (2840909090909091/250000000000000000)
  q := (42602816808281585737/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14520]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14520]

theorem width_14521 : mW 14521 = 368967266682801 := by
  have hu : mW 14521 ≤ 368967266682801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14521 ≤ 368967266682800 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14521 : RowArithmetic 14521 (55420094990975014911/50000000000000000000000) (150901779415802807715937/250000000000000000000000) (6651390320379387/1000000000000000000000000) where
  r0 := (114297098979/200000000000000000)
  k0 := (893472887490971/250000000000000000)
  k6 := (11363245074055351/1000000000000000000)
  q := (170417135288679230867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14521]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14521]

theorem width_14522 : mW 14522 = 369056206604470 := by
  have hu : mW 14522 ≤ 369056206604470 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14522 ≤ 369056206604469 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14522 : RowArithmetic 14522 (277093520409991898857/250000000000000000000000) (301798271828254347191709/500000000000000000000000) (6650199209147951/1000000000000000000000000) where
  r0 := (142856616571/250000000000000000)
  k0 := (55839171436901/15625000000000000)
  k6 := (11362853824891943/1000000000000000000)
  q := (42605750785545371023/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14522]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14522]

theorem width_14523 : mW 14523 = 369145161838695 := by
  have hu : mW 14523 ≤ 369145161838695 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14523 ≤ 369145161838694 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14523 : RowArithmetic 14523 (1108346269869218599133/1000000000000000000000000) (603585971094170145973189/1000000000000000000000000) (3324504198032633/500000000000000000000000) where
  r0 := (285683723917/500000000000000000)
  k0 := (1786761208100421/500000000000000000)
  k6 := (710153913508699/62500000000000000)
  q := (42607217698413493097/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14523]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14523]

theorem width_14524 : mW 14524 = 369234132387058 := by
  have hu : mW 14524 ≤ 369234132387058 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14524 ≤ 369234132387057 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14524 : RowArithmetic 14524 (277079616126330085257/250000000000000000000000) (301787699987940159429013/500000000000000000000000) (6647817881035517/1000000000000000000000000) where
  r0 := (571308439543/1000000000000000000)
  k0 := (357333788267861/100000000000000000)
  k6 := (5681035723895059/500000000000000000)
  q := (170434738243117561929/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14524]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14524]

theorem width_14525 : mW 14525 = 369323118251141 := by
  have hu : mW 14525 ≤ 369323118251141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14525 ≤ 369323118251140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14525 : RowArithmetic 14525 (554145332773170299417/500000000000000000000000) (603564830301323978124149/1000000000000000000000000) (3323313831981461/500000000000000000000000) where
  r0 := (4462886261/7812500000000000)
  k0 := (446644171423629/125000000000000000)
  k6 := (1136168031983779/100000000000000000)
  q := (34088121098118623059/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14525]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14525]

theorem width_14526 : mW 14526 = 369412119432526 := by
  have hu : mW 14526 ≤ 369412119432526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14526 ≤ 369412119432525 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14526 : RowArithmetic 14526 (554131436495173947963/500000000000000000000000) (301777131035093031309413/500000000000000000000000) (6645437744751741/1000000000000000000000000) where
  r0 := (571190453427/1000000000000000000)
  k0 := (714593776465859/200000000000000000)
  k6 := (11361289232275247/1000000000000000000)
  q := (85223236268050745739/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14526]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14526]

theorem width_14527 : mW 14527 = 369501135932794 := by
  have hu : mW 14527 ≤ 369501135932794 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14527 ≤ 369501135932793 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14527 : RowArithmetic 14527 (554117543417705986487/500000000000000000000000) (75442961910268943849147/125000000000000000000000) (664424812330629/100000000000000000000000) where
  r0 := (571131475597/1000000000000000000)
  k0 := (3572784415493461/1000000000000000000)
  k6 := (11360898185095539/1000000000000000000)
  q := (85226169689831772939/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14527]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14527]

theorem width_14528 : mW 14528 = 369590167753527 := by
  have hu : mW 14528 ≤ 369590167753527 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14528 ≤ 369590167753526 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14528 : RowArithmetic 14528 (1108207307079602842981/1000000000000000000000000) (603533129936905549039887/1000000000000000000000000) (1328611759906181/200000000000000000000000) where
  r0 := (142768126979/250000000000000000)
  k0 := (893149992719679/250000000000000000)
  k6 := (11360507178291717/1000000000000000000)
  q := (42614551505325032577/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14528]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14528]

theorem width_14529 : mW 14529 = 369679214896308 := by
  have hu : mW 14529 ≤ 369679214896308 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14529 ≤ 369679214896307 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14529 : RowArithmetic 14529 (554089766860495395929/500000000000000000000000) (603522566034133241348233/1000000000000000000000000) (3320934886664971/500000000000000000000000) where
  r0 := (571013550381/1000000000000000000)
  k0 := (3572415548479117/1000000000000000000)
  k6 := (11360116211856833/1000000000000000000)
  q := (17046407246103209299/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14529]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14529]

theorem width_14530 : mW 14530 = 369768277362718 := by
  have hu : mW 14530 ≤ 369768277362718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14530 ≤ 369768277362717 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14530 : RowArithmetic 14530 (1108151766757647793329/1000000000000000000000000) (603512003573519900114819/1000000000000000000000000) (6640681044607833/1000000000000000000000000) where
  r0 := (570954602991/1000000000000000000)
  k0 := (1786115574147489/500000000000000000)
  k6 := (567986264289197/50000000000000000)
  q := (85234969349440139281/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14530]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14530]

theorem width_14531 : mW 14531 = 369857355154340 := by
  have hu : mW 14531 ≤ 369857355154340 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14531 ≤ 369857355154339 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14531 : RowArithmetic 14531 (1108124006187645621653/1000000000000000000000000) (75437680319343865879297/125000000000000000000000) (1659873153317253/250000000000000000000000) where
  r0 := (570895665741/1000000000000000000)
  k0 := (714409354062819/200000000000000000)
  k6 := (2271866880013219/200000000000000000)
  q := (170475804734865528073/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14531]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14531]

theorem width_14532 : mW 14532 = 369946448272755 := by
  have hu : mW 14532 ≤ 369946448272755 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14532 ≤ 369946448272754 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14532 : RowArithmetic 14532 (1108096252009057737401/1000000000000000000000000) (301745441488755877869001/500000000000000000000000) (3319152239608993/500000000000000000000000) where
  r0 := (570836738631/1000000000000000000)
  k0 := (3571862414539907/1000000000000000000)
  k6 := (2839735888674089/250000000000000000)
  q := (170481670569008678987/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14532]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14532]

theorem width_14533 : mW 14533 = 370035556719546 := by
  have hu : mW 14533 ≤ 370035556719546 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14533 ≤ 370035556719545 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14533 : RowArithmetic 14533 (34627140756873668803/31250000000000000000000) (603480324841487955409589/1000000000000000000000000) (3318558321179633/500000000000000000000000) where
  r0 := (570777821657/1000000000000000000)
  k0 := (1785839040481669/500000000000000000)
  k6 := (567927637483389/50000000000000000)
  q := (34097507240266113037/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14533]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14533]

theorem width_14534 : mW 14534 = 370124680496295 := by
  have hu : mW 14534 ≤ 370124680496295 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14534 ≤ 370124680496294 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14534 : RowArithmetic 14534 (110804076281841908979/100000000000000000000000) (150867442036591298324663/250000000000000000000000) (3317964551298709/500000000000000000000000) where
  r0 := (285359457409/500000000000000000)
  k0 := (446436721198087/125000000000000000)
  k6 := (1135816198497343/100000000000000000)
  q := (170493401631852016961/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14534]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14534]

theorem width_14535 : mW 14535 = 370213819604584 := by
  have hu : mW 14535 ≤ 370213819604584 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14535 ≤ 370213819604583 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14535 : RowArithmetic 14535 (1108013027802518019253/1000000000000000000000000) (603459212891829221934379/1000000000000000000000000) (6634741859837049/1000000000000000000000000) where
  r0 := (57066001811/100000000000000000)
  k0 := (1785654740197451/500000000000000000)
  k6 := (11357771260606367/1000000000000000000)
  q := (17049926686059386103/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14535]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14535]

theorem width_14536 : mW 14536 = 370302974045995 := by
  have hu : mW 14536 ≤ 370302974045995 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14536 ≤ 370302974045994 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14536 : RowArithmetic 14536 (1107985299170330149603/1000000000000000000000000) (603448659077565904104873/1000000000000000000000000) (6633554913982801/1000000000000000000000000) where
  r0 := (142650282883/250000000000000000)
  k0 := (3571125213394261/1000000000000000000)
  k6 := (1419672572069957/125000000000000000)
  q := (85252565943788460261/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14536]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14536]

theorem width_14537 : mW 14537 = 370392143822112 := by
  have hu : mW 14537 ≤ 370392143822112 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14537 ≤ 370392143822111 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14537 : RowArithmetic 14537 (110795757691993124169/100000000000000000000000) (603438106703261129753911/1000000000000000000000000) (6632368264939321/1000000000000000000000000) where
  r0 := (14263556377/25000000000000000)
  k0 := (357094096857369/100000000000000000)
  k6 := (5678494966413181/500000000000000000)
  q := (85255498356411007493/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14537]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14537]

theorem width_14538 : mW 14538 = 370481328934516 := by
  have hu : mW 14538 ≤ 370481328934516 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14538 ≤ 370481328934515 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14538 : RowArithmetic 14538 (276982465262349802221/250000000000000000000000) (603427555768601014484673/1000000000000000000000000) (3315590956305673/500000000000000000000000) where
  r0 := (570483388753/1000000000000000000)
  k0 := (1785378372966747/500000000000000000)
  k6 := (11356599329399553/1000000000000000000)
  q := (21314607667043745049/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14538]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14538]

theorem width_14539 : mW 14539 = 370570529384790 := by
  have hu : mW 14539 ≤ 370570529384790 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14539 ≤ 370570529384789 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14539 : RowArithmetic 14539 (276975537889202941287/250000000000000000000000) (1885678144603973683111/3125000000000000000000) (6629995856903619/1000000000000000000000000) where
  r0 := (570424532547/1000000000000000000)
  k0 := (1785286272732293/500000000000000000)
  k6 := (5678104383136149/500000000000000000)
  q := (170522725758181569129/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14539]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14539]

theorem width_14540 : mW 14540 = 370659745174516 := by
  have hu : mW 14540 ≤ 370659745174516 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14540 ≤ 370659745174515 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14540 : RowArithmetic 14540 (1107874448440247835227/1000000000000000000000000) (603406458216959141518773/1000000000000000000000000) (3314405048860467/500000000000000000000000) where
  r0 := (285182843231/500000000000000000)
  k0 := (1785194183585199/500000000000000000)
  k6 := (2838954560859417/250000000000000000)
  q := (21316073747292206251/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14540]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14540]

theorem width_14541 : mW 14541 = 370748976305278 := by
  have hu : mW 14541 ≤ 370748976305278 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14541 ≤ 370748976305277 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14541 : RowArithmetic 14541 (276961687924446536307/250000000000000000000000) (150848977899837495226903/250000000000000000000000) (6627624634968093/1000000000000000000000000) where
  r0 := (570306850493/1000000000000000000)
  k0 := (446275526379839/125000000000000000)
  k6 := (2271085552177747/200000000000000000)
  q := (170534453996839008263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14541]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14541]

theorem width_14542 : mW 14542 = 370838222778657 := by
  have hu : mW 14542 ≤ 370838222778657 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14542 ≤ 370838222778656 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14542 : RowArithmetic 14542 (1107819061327507570043/1000000000000000000000000) (150846341605032628797437/250000000000000000000000) (1325287893709997/200000000000000000000000) where
  r0 := (570248024639/1000000000000000000)
  k0 := (3570020077069827/1000000000000000000)
  k6 := (11355037318618573/1000000000000000000)
  q := (3410806356274128911/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14542]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14542]

theorem width_14543 : mW 14543 = 370927484596236 := by
  have hu : mW 14543 ≤ 370927484596236 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14543 ≤ 370927484596235 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14543 : RowArithmetic 14543 (1107791377327492785187/1000000000000000000000000) (60337482267898720819377/100000000000000000000000) (3312627299185753/500000000000000000000000) where
  r0 := (570189208897/1000000000000000000)
  k0 := (3569835965257781/1000000000000000000)
  k6 := (11354646916620259/1000000000000000000)
  q := (170546181428960759949/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14543]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14543]

theorem width_14544 : mW 14544 = 371016761759599 := by
  have hu : mW 14544 ≤ 371016761759599 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14544 ≤ 371016761759598 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14544 : RowArithmetic 14544 (1107763699695822737119/1000000000000000000000000) (603364280375606710367901/1000000000000000000000000) (207002188260549/31250000000000000000000) where
  r0 := (114026080653/200000000000000000)
  k0 := (1784825937799871/500000000000000000)
  k6 := (11354256554886869/1000000000000000000)
  q := (42638011210655686491/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14544]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14544]

theorem width_14545 : mW 14545 = 371106054270328 := by
  have hu : mW 14545 ≤ 371106054270328 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14545 ≤ 371106054270327 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14545 : RowArithmetic 14545 (1107736028430580049663/1000000000000000000000000) (603353739509675674545193/1000000000000000000000000) (165572143658829/25000000000000000000000) where
  r0 := (570071607741/1000000000000000000)
  k0 := (28555742464743/8000000000000000)
  k6 := (11353866233411483/1000000000000000000)
  q := (170557908054713194527/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14545]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14545]

theorem width_14546 : mW 14546 = 371195362130006 := by
  have hu : mW 14546 ≤ 371195362130006 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14546 ≤ 371195362130005 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14546 : RowArithmetic 14546 (553854181764923808239/500000000000000000000000) (60334320008088089750059/100000000000000000000000) (6621701764323291/1000000000000000000000000) where
  r0 := (570012822321/1000000000000000000)
  k0 := (713856752545617/200000000000000000)
  k6 := (5676737976093591/500000000000000000)
  q := (34112754213050578599/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14546]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14546]

theorem width_14547 : mW 14547 = 371284685340216 := by
  have hu : mW 14547 ≤ 371284685340216 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14547 ≤ 371284685340215 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14547 : RowArithmetic 14547 (1107680704991709069863/1000000000000000000000000) (603332662088909259547493/1000000000000000000000000) (6620518078153007/1000000000000000000000000) where
  r0 := (142488511751/250000000000000000)
  k0 := (713819947901133/200000000000000000)
  k6 := (11353085711207047/1000000000000000000)
  q := (170569633874262625153/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14547]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14547]

theorem width_14548 : mW 14548 = 371374023902540 := by
  have hu : mW 14548 ≤ 371374023902540 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14548 ≤ 371374023902539 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14548 : RowArithmetic 14548 (276913263203562312113/250000000000000000000000) (150830531383361931067923/250000000000000000000000) (661933468774741/100000000000000000000000) where
  r0 := (569895281787/1000000000000000000)
  k0 := (3568915738419647/1000000000000000000)
  k6 := (2838173877616041/250000000000000000)
  q := (42643874120440792803/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14548]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14548]

theorem width_14549 : mW 14549 = 371463377818563 := by
  have hu : mW 14549 ≤ 371463377818563 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14549 ≤ 371463377818562 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14549 : RowArithmetic 14549 (69226587937222020277/62500000000000000000000) (301655795207091690793809/500000000000000000000000) (1654537898252897/250000000000000000000000) where
  r0 := (569836526667/1000000000000000000)
  k0 := (3568731759464061/1000000000000000000)
  k6 := (5676152674975809/500000000000000000)
  q := (34116271777555061563/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14549]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14549]

theorem width_14550 : mW 14550 = 371552747089866 := by
  have hu : mW 14550 ≤ 371552747089866 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14550 ≤ 371552747089865 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14550 : RowArithmetic 14550 (221519553506741015951/200000000000000000000000) (120660211346160672384067/200000000000000000000000) (3308484396925369/500000000000000000000000) where
  r0 := (569777781643/1000000000000000000)
  k0 := (3568547802639199/1000000000000000000)
  k6 := (354747350926953/31250000000000000)
  q := (85293610546159904017/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14550]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14550]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14476 then ⟨(277415095617695328981/250000000000000000000000), (604084448012335624369593/1000000000000000000000000), (6705300470686649/1000000000000000000000000)⟩ else
  if n = 14477 then ⟨(1109632273883784460411/1000000000000000000000000), (75509226085174469544169/125000000000000000000000), (6704095842983199/1000000000000000000000000)⟩ else
  if n = 14478 then ⟨(1109604171793298928187/1000000000000000000000000), (30203158540455300565593/50000000000000000000000), (3351445758889623/500000000000000000000000)⟩ else
  if n = 14479 then ⟨(221915215239471662589/200000000000000000000000), (604052534395146865879417/1000000000000000000000000), (3350843747488617/500000000000000000000000)⟩ else
  if n = 14480 then ⟨(1109547987093998413589/1000000000000000000000000), (12080837988783974602989/20000000000000000000000), (837560471809963/125000000000000000000000)⟩ else
  if n = 14481 then ⟨(1109519904481254826911/1000000000000000000000000), (604031265940942336517287/1000000000000000000000000), (16748200890473/2500000000000000000000)⟩ else
  if n = 14482 then ⟨(277372957089291097747/250000000000000000000000), (75502579237507288346617/125000000000000000000000), (3349038620004161/500000000000000000000000)⟩ else
  if n = 14483 then ⟨(554731879359882111497/500000000000000000000000), (604010003316227562776669/1000000000000000000000000), (1674218606459923/250000000000000000000000)⟩ else
  if n = 14484 then ⟨(1109435695567092200013/1000000000000000000000000), (120799874837826183745057/200000000000000000000000), (6695671913585971/1000000000000000000000000)⟩ else
  if n = 14485 then ⟨(1109407638897187918733/1000000000000000000000000), (603988746518449436848637/1000000000000000000000000), (1338893940629979/200000000000000000000000)⟩ else
  if n = 14486 then ⟨(554689794354045386881/500000000000000000000000), (301989060151932085576943/500000000000000000000000), (1338653558886841/200000000000000000000000)⟩ else
  if n = 14487 then ⟨(13866894312473011481/12500000000000000000000), (75495936943132044248727/125000000000000000000000), (83650827341771/12500000000000000000000)⟩ else
  if n = 14488 then ⟨(1109323507764479264661/1000000000000000000000000), (30197843612085362159371/50000000000000000000000), (209089527555473/31250000000000000000000)⟩ else
  if n = 14489 then ⟨(110929547700604748209/100000000000000000000000), (603946250393498244217531/1000000000000000000000000), (6689663877637433/1000000000000000000000000)⟩ else
  if n = 14490 then ⟨(554633726360294238631/500000000000000000000000), (603935630000110869197621/1000000000000000000000000), (6688463174831483/1000000000000000000000000)⟩ else
  if n = 14491 then ⟨(44369577396245817371/40000000000000000000000), (301962505530613323116177/500000000000000000000000), (104488480832191/15625000000000000000000)⟩ else
  if n = 14492 then ⟨(55460571178038090771/50000000000000000000000), (120782878715305460326547/200000000000000000000000), (1671515668206653/250000000000000000000000)⟩ else
  if n = 14493 then ⟨(1109183418682482797247/1000000000000000000000000), (9435996524151477089369/15625000000000000000000), (3342431436716839/500000000000000000000000)⟩ else
  if n = 14494 then ⟨(554577710134676916677/500000000000000000000000), (603893162968410251650779/1000000000000000000000000), (1670915843746119/250000000000000000000000)⟩ else
  if n = 14495 then ⟨(221825485663884226617/200000000000000000000000), (603882549844356456651857/1000000000000000000000000), (3341232088691049/500000000000000000000000)⟩ else
  if n = 14496 then ⟨(1109099442830731183229/1000000000000000000000000), (150967984543303784847731/250000000000000000000000), (6681265280529657/1000000000000000000000000)⟩ else
  if n = 14497 then ⟨(1109071463801332181791/1000000000000000000000000), (603861327954668485250067/1000000000000000000000000), (3340033342165171/500000000000000000000000)⟩ else
  if n = 14498 then ⟨(1109043491229271648009/1000000000000000000000000), (603850719188398746465483/1000000000000000000000000), (3339434194343663/500000000000000000000000)⟩ else
  if n = 14499 then ⟨(44360621004503971557/40000000000000000000000), (603840111874088210289259/1000000000000000000000000), (3338835196751937/500000000000000000000000)⟩ else
  if n = 14500 then ⟨(1108987565449365087521/1000000000000000000000000), (603829506011419379714901/1000000000000000000000000), (1669118174670819/250000000000000000000000)⟩ else
  if n = 14501 then ⟨(1108959612237618826337/1000000000000000000000000), (60381890160007475480077/100000000000000000000000), (6675275304128819/1000000000000000000000000)⟩ else
  if n = 14502 then ⟨(554465832737706236431/500000000000000000000000), (966093277823579207983/1600000000000000000000), (6674078209743889/1000000000000000000000000)⟩ else
  if n = 14503 then ⟨(1108903725160797793391/1000000000000000000000000), (301898848565044389686269/500000000000000000000000), (6672881415431871/1000000000000000000000000)⟩ else
  if n = 14504 then ⟨(277218947822956707739/250000000000000000000000), (603787097070812977677479/1000000000000000000000000), (1667921230274043/250000000000000000000000)⟩ else
  if n = 14505 then ⟨(138605982983319285859/125000000000000000000000), (301888249230796231407651/500000000000000000000000), (6670488726640311/1000000000000000000000000)⟩ else
  if n = 14506 then ⟨(554409971441516616257/500000000000000000000000), (120753180260422051046747/200000000000000000000000), (3334646415983877/500000000000000000000000)⟩ else
  if n = 14507 then ⟨(44351681133572775841/40000000000000000000000), (15093882639801236790899/25000000000000000000000), (6668097236982079/1000000000000000000000000)⟩ else
  if n = 14508 then ⟨(17324439378647927393/15625000000000000000000), (603744711331093282756441/1000000000000000000000000), (6666901941586831/1000000000000000000000000)⟩ else
  if n = 14509 then ⟨(1108736218563534809567/1000000000000000000000000), (18866691203716406707383/31250000000000000000000), (1666426736421421/250000000000000000000000)⟩ else
  if n = 14510 then ⟨(554354161663788684037/500000000000000000000000), (150930881788807011087507/250000000000000000000000), (6664512249182241/1000000000000000000000000)⟩ else
  if n = 14511 then ⟨(554340217261827117279/500000000000000000000000), (603712937239685827602391/1000000000000000000000000), (3331658925990127/500000000000000000000000)⟩ else
  if n = 14512 then ⟨(554326276074911256791/500000000000000000000000), (120740469754396394530917/200000000000000000000000), (1332424750796681/200000000000000000000000)⟩ else
  if n = 14513 then ⟨(221724935240828581949/200000000000000000000000), (37730735109487511610709/62500000000000000000000), (6660929955095523/1000000000000000000000000)⟩ else
  if n = 14514 then ⟨(1108596806684674027867/1000000000000000000000000), (603681176178824203483291/1000000000000000000000000), (6659736455220367/1000000000000000000000000)⟩ else
  if n = 14515 then ⟨(277142235897369398871/250000000000000000000000), (60367059205273787288143/100000000000000000000000), (266341730170473/40000000000000000000000)⟩ else
  if n = 14516 then ⟨(554270543458307332469/500000000000000000000000), (60366000937322514889439/100000000000000000000000), (665735035212377/100000000000000000000000)⟩ else
  if n = 14517 then ⟨(69282077291509189849/62500000000000000000000), (301824714069985063743041/500000000000000000000000), (3328078874355057/500000000000000000000000)⟩ else
  if n = 14518 then ⟨(1108485392830137737129/1000000000000000000000000), (301819424176328472832089/500000000000000000000000), (831870680490603/125000000000000000000000)⟩ else
  if n = 14519 then ⟨(55422877770632526739/50000000000000000000000), (603628270010969835204361/1000000000000000000000000), (665377343767191/100000000000000000000000)⟩ else
  if n = 14520 then ⟨(55421486220487473777/50000000000000000000000), (603617693114593097570289/1000000000000000000000000), (1663145432463849/250000000000000000000000)⟩ else
  if n = 14521 then ⟨(55420094990975014911/50000000000000000000000), (150901779415802807715937/250000000000000000000000), (6651390320379387/1000000000000000000000000)⟩ else
  if n = 14522 then ⟨(277093520409991898857/250000000000000000000000), (301798271828254347191709/500000000000000000000000), (6650199209147951/1000000000000000000000000)⟩ else
  if n = 14523 then ⟨(1108346269869218599133/1000000000000000000000000), (603585971094170145973189/1000000000000000000000000), (3324504198032633/500000000000000000000000)⟩ else
  if n = 14524 then ⟨(277079616126330085257/250000000000000000000000), (301787699987940159429013/500000000000000000000000), (6647817881035517/1000000000000000000000000)⟩ else
  if n = 14525 then ⟨(554145332773170299417/500000000000000000000000), (603564830301323978124149/1000000000000000000000000), (3323313831981461/500000000000000000000000)⟩ else
  if n = 14526 then ⟨(554131436495173947963/500000000000000000000000), (301777131035093031309413/500000000000000000000000), (6645437744751741/1000000000000000000000000)⟩ else
  if n = 14527 then ⟨(554117543417705986487/500000000000000000000000), (75442961910268943849147/125000000000000000000000), (664424812330629/100000000000000000000000)⟩ else
  if n = 14528 then ⟨(1108207307079602842981/1000000000000000000000000), (603533129936905549039887/1000000000000000000000000), (1328611759906181/200000000000000000000000)⟩ else
  if n = 14529 then ⟨(554089766860495395929/500000000000000000000000), (603522566034133241348233/1000000000000000000000000), (3320934886664971/500000000000000000000000)⟩ else
  if n = 14530 then ⟨(1108151766757647793329/1000000000000000000000000), (603512003573519900114819/1000000000000000000000000), (6640681044607833/1000000000000000000000000)⟩ else
  if n = 14531 then ⟨(1108124006187645621653/1000000000000000000000000), (75437680319343865879297/125000000000000000000000), (1659873153317253/250000000000000000000000)⟩ else
  if n = 14532 then ⟨(1108096252009057737401/1000000000000000000000000), (301745441488755877869001/500000000000000000000000), (3319152239608993/500000000000000000000000)⟩ else
  if n = 14533 then ⟨(34627140756873668803/31250000000000000000000), (603480324841487955409589/1000000000000000000000000), (3318558321179633/500000000000000000000000)⟩ else
  if n = 14534 then ⟨(110804076281841908979/100000000000000000000000), (150867442036591298324663/250000000000000000000000), (3317964551298709/500000000000000000000000)⟩ else
  if n = 14535 then ⟨(1108013027802518019253/1000000000000000000000000), (603459212891829221934379/1000000000000000000000000), (6634741859837049/1000000000000000000000000)⟩ else
  if n = 14536 then ⟨(1107985299170330149603/1000000000000000000000000), (603448659077565904104873/1000000000000000000000000), (6633554913982801/1000000000000000000000000)⟩ else
  if n = 14537 then ⟨(110795757691993124169/100000000000000000000000), (603438106703261129753911/1000000000000000000000000), (6632368264939321/1000000000000000000000000)⟩ else
  if n = 14538 then ⟨(276982465262349802221/250000000000000000000000), (603427555768601014484673/1000000000000000000000000), (3315590956305673/500000000000000000000000)⟩ else
  if n = 14539 then ⟨(276975537889202941287/250000000000000000000000), (1885678144603973683111/3125000000000000000000), (6629995856903619/1000000000000000000000000)⟩ else
  if n = 14540 then ⟨(1107874448440247835227/1000000000000000000000000), (603406458216959141518773/1000000000000000000000000), (3314405048860467/500000000000000000000000)⟩ else
  if n = 14541 then ⟨(276961687924446536307/250000000000000000000000), (150848977899837495226903/250000000000000000000000), (6627624634968093/1000000000000000000000000)⟩ else
  if n = 14542 then ⟨(1107819061327507570043/1000000000000000000000000), (150846341605032628797437/250000000000000000000000), (1325287893709997/200000000000000000000000)⟩ else
  if n = 14543 then ⟨(1107791377327492785187/1000000000000000000000000), (60337482267898720819377/100000000000000000000000), (3312627299185753/500000000000000000000000)⟩ else
  if n = 14544 then ⟨(1107763699695822737119/1000000000000000000000000), (603364280375606710367901/1000000000000000000000000), (207002188260549/31250000000000000000000)⟩ else
  if n = 14545 then ⟨(1107736028430580049663/1000000000000000000000000), (603353739509675674545193/1000000000000000000000000), (165572143658829/25000000000000000000000)⟩ else
  if n = 14546 then ⟨(553854181764923808239/500000000000000000000000), (60334320008088089750059/100000000000000000000000), (6621701764323291/1000000000000000000000000)⟩ else
  if n = 14547 then ⟨(1107680704991709069863/1000000000000000000000000), (603332662088909259547493/1000000000000000000000000), (6620518078153007/1000000000000000000000000)⟩ else
  if n = 14548 then ⟨(276913263203562312113/250000000000000000000000), (150830531383361931067923/250000000000000000000000), (661933468774741/100000000000000000000000)⟩ else
  if n = 14549 then ⟨(69226587937222020277/62500000000000000000000), (301655795207091690793809/500000000000000000000000), (1654537898252897/250000000000000000000000)⟩ else
  ⟨(221519553506741015951/200000000000000000000000), (120660211346160672384067/200000000000000000000000), (3308484396925369/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14476 ≤ n) (hb : n ≤ 14550) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14476
  · exact row_14477
  · exact row_14478
  · exact row_14479
  · exact row_14480
  · exact row_14481
  · exact row_14482
  · exact row_14483
  · exact row_14484
  · exact row_14485
  · exact row_14486
  · exact row_14487
  · exact row_14488
  · exact row_14489
  · exact row_14490
  · exact row_14491
  · exact row_14492
  · exact row_14493
  · exact row_14494
  · exact row_14495
  · exact row_14496
  · exact row_14497
  · exact row_14498
  · exact row_14499
  · exact row_14500
  · exact row_14501
  · exact row_14502
  · exact row_14503
  · exact row_14504
  · exact row_14505
  · exact row_14506
  · exact row_14507
  · exact row_14508
  · exact row_14509
  · exact row_14510
  · exact row_14511
  · exact row_14512
  · exact row_14513
  · exact row_14514
  · exact row_14515
  · exact row_14516
  · exact row_14517
  · exact row_14518
  · exact row_14519
  · exact row_14520
  · exact row_14521
  · exact row_14522
  · exact row_14523
  · exact row_14524
  · exact row_14525
  · exact row_14526
  · exact row_14527
  · exact row_14528
  · exact row_14529
  · exact row_14530
  · exact row_14531
  · exact row_14532
  · exact row_14533
  · exact row_14534
  · exact row_14535
  · exact row_14536
  · exact row_14537
  · exact row_14538
  · exact row_14539
  · exact row_14540
  · exact row_14541
  · exact row_14542
  · exact row_14543
  · exact row_14544
  · exact row_14545
  · exact row_14546
  · exact row_14547
  · exact row_14548
  · exact row_14549
  · exact row_14550

end BstLean.Part271.R3.Rows14476
