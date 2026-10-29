import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14075–14149. -/
namespace BstLean.Part271.R3.Rows14075
open Real BstLean.Part130 BstLean.Part227

theorem width_14075 : mW 14075 = 330802979346923 := by
  have hu : mW 14075 ≤ 330802979346923 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14075 ≤ 330802979346922 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14075 : RowArithmetic 14075 (1121477666316462770833/1000000000000000000000000) (304235978450427757088357/500000000000000000000000) (1442767489484229/200000000000000000000000) where
  r0 := (598862880229/1000000000000000000)
  k0 := (3658494960105611/1000000000000000000)
  k6 := (2308375360040459/200000000000000000)
  q := (20972452169453146711/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14075]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14075]

theorem width_14076 : mW 14076 = 330885246718607 := by
  have hu : mW 14076 ≤ 330885246718607 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14076 ≤ 330885246718606 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14076 : RowArithmetic 14076 (1121446785876102430851/1000000000000000000000000) (608460705811791933913977/1000000000000000000000000) (7212503221233977/1000000000000000000000000) where
  r0 := (7484988299/12500000000000000)
  k0 := (3658300025778641/1000000000000000000)
  k6 := (11541466808663519/1000000000000000000)
  q := (83892788724657377431/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14076]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14076]

theorem width_14077 : mW 14077 = 330967528702872 := by
  have hu : mW 14077 ≤ 330967528702872 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14077 ≤ 330967528702871 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14077 : RowArithmetic 14077 (1121415912783382642037/1000000000000000000000000) (608449456317684495331329/1000000000000000000000000) (1802792334987331/250000000000000000000000) where
  r0 := (119747051789/200000000000000000)
  k0 := (914526278921933/250000000000000000)
  k6 := (1442632107601613/125000000000000000)
  q := (16779153733129689637/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14077]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14077]

theorem width_14078 : mW 14078 = 331049825301276 := by
  have hu : mW 14078 ≤ 331049825301276 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14078 ≤ 331049825301275 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14078 : RowArithmetic 14078 (280346261759003635717/250000000000000000000000) (152109552104543000549367/250000000000000000000000) (1441967160690543/200000000000000000000000) where
  r0 := (598671465299/1000000000000000000)
  k0 := (3657910229821483/1000000000000000000)
  k6 := (1154064695664269/100000000000000000)
  q := (41949374250398539169/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14078]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14078]

theorem width_14079 : mW 14079 = 331132136515375 := by
  have hu : mW 14079 ≤ 331132136515375 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14079 ≤ 331132136515374 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14079 : RowArithmetic 14079 (112135418863171131729/100000000000000000000000) (304213481056446659532051/500000000000000000000000) (3604251305814883/500000000000000000000000) where
  r0 := (598607682981/1000000000000000000)
  k0 := (3657715368180711/1000000000000000000)
  k6 := (5770118548072561/500000000000000000)
  q := (167803456460229090241/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14079]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14079]

theorem width_14080 : mW 14080 = 331214462346727 := by
  have hu : mW 14080 ≤ 331214462346727 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14080 ≤ 331214462346726 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14080 : RowArithmetic 14080 (560661668784092963421/500000000000000000000000) (608415717401487438968861/1000000000000000000000000) (72071697643661/10000000000000000000000) where
  r0 := (149635977997/250000000000000000)
  k0 := (1828760265380061/500000000000000000)
  k6 := (2884956819828111/250000000000000000)
  q := (167809415707224247519/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14080]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14080]

theorem width_14081 : mW 14081 = 331296802796890 := by
  have hu : mW 14081 ≤ 331296802796890 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14081 ≤ 331296802796889 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14081 : RowArithmetic 14081 (560646246921576122297/500000000000000000000000) (152101118570898370676709/250000000000000000000000) (7205837261547387/1000000000000000000000000) where
  r0 := (598480152317/1000000000000000000)
  k0 := (182866285877721/50000000000000000)
  k6 := (2307883501227381/200000000000000000)
  q := (167815374742602174961/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14081]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14081]

theorem width_14082 : mW 14082 = 331379157867421 := by
  have hu : mW 14082 ≤ 331379157867421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14082 ≤ 331379157867420 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14082 : RowArithmetic 14082 (280315414363581405119/250000000000000000000000) (304196616379425310316799/500000000000000000000000) (1440901020611873/200000000000000000000000) where
  r0 := (299208201983/500000000000000000)
  k0 := (914282732140341/250000000000000000)
  k6 := (11539007776610753/1000000000000000000)
  q := (20977666695798176877/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14082]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14082]

theorem width_14083 : mW 14083 = 331461527559877 := by
  have hu : mW 14083 ≤ 331461527559877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14083 ≤ 331461527559876 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14083 : RowArithmetic 14083 (1121230828399422314073/1000000000000000000000000) (608381992826898223231659/1000000000000000000000000) (7203173288787821/1000000000000000000000000) where
  r0 := (59835266693/100000000000000000)
  k0 := (3656936163769543/1000000000000000000)
  k6 := (72116238067039/6250000000000000)
  q := (10489205761162281633/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14083]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14083]

theorem width_14084 : mW 14084 = 331543911875816 := by
  have hu : mW 14084 ≤ 331543911875816 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14084 ≤ 331543911875815 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14084 : RowArithmetic 14084 (1121200006676158928831/1000000000000000000000000) (608370754487375713749969/1000000000000000000000000) (3600920909309283/500000000000000000000000) where
  r0 := (74786117651/125000000000000000)
  k0 := (3656741423179769/1000000000000000000)
  k6 := (11538188448475619/1000000000000000000)
  q := (20979156322407247843/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14084]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14084]

theorem width_14085 : mW 14085 = 331626310816796 := by
  have hu : mW 14085 ≤ 331626310816796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14085 ≤ 331626310816795 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14085 : RowArithmetic 14085 (280292298070563244463/250000000000000000000000) (608359517739922649199223/1000000000000000000000000) (7200510692437461/1000000000000000000000000) where
  r0 := (598225226797/1000000000000000000)
  k0 := (182827335339337/50000000000000000)
  k6 := (5768889424925573/500000000000000000)
  q := (41959802192098093827/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14085]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14085]

theorem width_14086 : mW 14086 = 331708724384374 := by
  have hu : mW 14086 ≤ 331708724384374 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14086 ≤ 331708724384373 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14086 : RowArithmetic 14086 (1121138385215423448289/1000000000000000000000000) (38021767661511168529281/62500000000000000000000) (7199179910130433/1000000000000000000000000) where
  r0 := (598161523693/1000000000000000000)
  k0 := (228522000911381/62500000000000000)
  k6 := (2884342323711269/250000000000000000)
  q := (83922583373011105133/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14086]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14086]

theorem width_14087 : mW 14087 = 331791152580108 := by
  have hu : mW 14087 ≤ 331791152580108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14087 ≤ 331791152580107 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14087 : RowArithmetic 14087 (560553792736694835227/500000000000000000000000) (608337049019783666973509/1000000000000000000000000) (7197849471583437/1000000000000000000000000) where
  r0 := (119619566379/200000000000000000)
  k0 := (731231469313329/200000000000000000)
  k6 := (1153695978344967/100000000000000000)
  q := (41962781128042502517/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14087]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14087]

theorem width_14088 : mW 14088 = 331873595405555 := by
  have hu : mW 14088 ≤ 331873595405555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14088 ≤ 331873595405554 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14088 : RowArithmetic 14088 (224215358610774489461/200000000000000000000000) (304162908523188685374333/500000000000000000000000) (14055701907583/1953125000000000000000) where
  r0 := (598034151399/1000000000000000000)
  k0 := (146238508109281/40000000000000000)
  k6 := (2884137578914297/250000000000000000)
  q := (167857082066858293163/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14088]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14088]

theorem width_14089 : mW 14089 = 331956052862274 := by
  have hu : mW 14089 ≤ 331956052862274 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14089 ≤ 331956052862273 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14089 : RowArithmetic 14089 (1121046007954592360333/1000000000000000000000000) (608314586663599842118267/1000000000000000000000000) (3597594812656819/500000000000000000000000) where
  r0 := (597970482203/1000000000000000000)
  k0 := (228485505192249/62500000000000000)
  k6 := (2884035222864973/250000000000000000)
  q := (20982879926263696751/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14089]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14089]

theorem width_14090 : mW 14090 = 332038524951822 := by
  have hu : mW 14090 ≤ 332038524951822 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14090 ≤ 332038524951821 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14090 : RowArithmetic 14090 (56050761508663601357/50000000000000000000000) (1520758394677728022947/2500000000000000000000) (359693010868149/50000000000000000000000) where
  r0 := (597906824303/1000000000000000000)
  k0 := (913893371897539/250000000000000000)
  k6 := (11535731510850049/1000000000000000000)
  q := (167868996541946363063/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14090]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14090]

theorem width_14091 : mW 14091 = 332121011675757 := by
  have hu : mW 14091 ≤ 332121011675757 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14091 ≤ 332121011675756 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14091 : RowArithmetic 14091 (22419689194152688151/20000000000000000000000) (608292130668491687437287/1000000000000000000000000) (3596265576358333/500000000000000000000000) where
  r0 := (597843177697/1000000000000000000)
  k0 := (1827689458136143/500000000000000000)
  k6 := (11535322173819923/1000000000000000000)
  q := (83937476731195583397/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14091]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14091]

theorem width_14092 : mW 14092 = 332203513035637 := by
  have hu : mW 14092 ≤ 332203513035637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14092 ≤ 332203513035636 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14092 : RowArithmetic 14092 (1120953696555403367779/1000000000000000000000000) (304140452527720796308747/500000000000000000000000) (3595601215630443/500000000000000000000000) where
  r0 := (298889771191/500000000000000000)
  k0 := (3655184369117063/1000000000000000000)
  k6 := (2306982576072357/200000000000000000)
  q := (6715236406858659507/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14092]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14092]

theorem width_14093 : mW 14093 = 332286029033021 := by
  have hu : mW 14093 ≤ 332286029033021 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14093 ≤ 332286029033020 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14093 : RowArithmetic 14093 (1120922940714303116733/1000000000000000000000000) (304134840515790683858787/500000000000000000000000) (3594937026440929/500000000000000000000000) where
  r0 := (119543183671/200000000000000000)
  k0 := (3654989846119173/1000000000000000000)
  k6 := (11534503630467903/1000000000000000000)
  q := (167886866669194824187/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14093]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14093]

theorem width_14094 : mW 14094 = 332368559669466 := by
  have hu : mW 14094 ≤ 332368559669466 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14094 ≤ 332368559669465 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14094 : RowArithmetic 14094 (560446096091029947849/500000000000000000000000) (304129229298275808827471/500000000000000000000000) (7188546017465887/1000000000000000000000000) where
  r0 := (298826152807/500000000000000000)
  k0 := (3654795347276357/1000000000000000000)
  k6 := (1441761803016319/125000000000000000)
  q := (8394641147779933541/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14094]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14094]

theorem width_14095 : mW 14095 = 332451104946531 := by
  have hu : mW 14095 ≤ 332451104946531 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14095 ≤ 332451104946530 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14095 : RowArithmetic 14095 (224172290191279944899/200000000000000000000000) (304123618874996486474073/500000000000000000000000) (3593609162449643/500000000000000000000000) where
  r0 := (149397176039/250000000000000000)
  k0 := (1827300436291649/500000000000000000)
  k6 := (2883421315335501/250000000000000000)
  q := (41974694757675129519/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14095]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14095]

theorem width_14096 : mW 14096 = 332533664865773 := by
  have hu : mW 14096 ≤ 332533664865773 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14096 ≤ 332533664865772 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14096 : RowArithmetic 14096 (560415358517525326729/500000000000000000000000) (304118009245773112189813/500000000000000000000000) (3592945487534227/500000000000000000000000) where
  r0 := (597525113977/1000000000000000000)
  k0 := (3654406422031621/1000000000000000000)
  k6 := (11533276142094537/1000000000000000000)
  q := (33580946978904570493/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14096]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14096]

theorem width_14097 : mW 14097 = 332616239428752 := by
  have hu : mW 14097 ≤ 332616239428752 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14097 ≤ 332616239428751 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14097 : RowArithmetic 14097 (560399995207869974581/500000000000000000000000) (608224800820852228196641/1000000000000000000000000) (112258811997809/15625000000000000000000) where
  r0 := (149365383769/250000000000000000)
  k0 := (3654211995622121/1000000000000000000)
  k6 := (2883216766595107/250000000000000000)
  q := (16791069054708815651/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14097]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14097]

theorem width_14098 : mW 14098 = 332698828637024 := by
  have hu : mW 14098 ≤ 332698828637024 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14098 ≤ 332698828637023 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14098 : RowArithmetic 14098 (140096158887024753987/125000000000000000000000) (304106792368776033735487/500000000000000000000000) (7183237303159769/1000000000000000000000000) where
  r0 := (74674745931/125000000000000000)
  k0 := (5709402489599/1562500000000000)
  k6 := (5766229017095979/500000000000000000)
  q := (41979161497104727187/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14098]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14098]

theorem width_14099 : mW 14099 = 332781432492149 := by
  have hu : mW 14099 ≤ 332781432492149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14099 ≤ 332781432492148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14099 : RowArithmetic 14099 (1120738559074153975891/1000000000000000000000000) (608202370241286758861403/1000000000000000000000000) (718191098085491/100000000000000000000000) where
  r0 := (149333602773/250000000000000000)
  k0 := (3653823215196133/1000000000000000000)
  k6 := (11532049045521409/1000000000000000000)
  q := (16792260121853758373/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14099]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14099]

theorem width_14100 : mW 14100 = 332864050995686 := by
  have hu : mW 14100 ≤ 332864050995686 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14100 ≤ 332864050995685 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14100 : RowArithmetic 14100 (35022120448354322547/31250000000000000000000) (608191157331697614031021/1000000000000000000000000) (3590292500415873/500000000000000000000000) where
  r0 := (119454173201/200000000000000000)
  k0 := (3653628861175113/1000000000000000000)
  k6 := (1441455012545133/125000000000000000)
  q := (8396427811873332601/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14100]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14100]

theorem width_14101 : mW 14101 = 332946684149192 := by
  have hu : mW 14101 ≤ 332946684149192 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14101 ≤ 332946684149191 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14101 : RowArithmetic 14101 (1120677156913483634963/1000000000000000000000000) (608179946008425924300703/1000000000000000000000000) (3589629681488457/500000000000000000000000) where
  r0 := (74650916523/125000000000000000)
  k0 := (114169829102343/31250000000000000)
  k6 := (11531231198703209/1000000000000000000)
  q := (839672555226142901/5000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14101]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14101]

theorem width_14102 : mW 14102 = 333029331954226 := by
  have hu : mW 14102 ≤ 333029331954226 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14102 ≤ 333029331954225 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14102 : RowArithmetic 14102 (140080808346290282629/125000000000000000000000) (76021092033889142441113/125000000000000000000000) (1435586813435411/200000000000000000000000) where
  r0 := (4777150477/8000000000000000)
  k0 := (730648045097467/200000000000000000)
  k6 := (11530822340540133/1000000000000000000)
  q := (167940465641845830867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14102]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14102]

theorem width_14103 : mW 14103 = 333111994412346 := by
  have hu : mW 14103 ≤ 333111994412346 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14103 ≤ 333111994412345 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14103 : RowArithmetic 14103 (1120615783915588007587/1000000000000000000000000) (152039382029850209977689/250000000000000000000000) (7176609113318877/1000000000000000000000000) where
  r0 := (597080298327/1000000000000000000)
  k0 := (1826522971906489/500000000000000000)
  k6 := (2882603381466031/250000000000000000)
  q := (83973210013670431319/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14103]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14103]

theorem width_14104 : mW 14104 = 333194671525112 := by
  have hu : mW 14104 ≤ 333194671525112 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14104 ≤ 333194671525111 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14104 : RowArithmetic 14104 (1120585108347014461971/1000000000000000000000000) (24325852862117227514047/40000000000000000000000) (3587642250644547/500000000000000000000000) where
  r0 := (597016798287/1000000000000000000)
  k0 := (228303230390411/62500000000000000)
  k6 := (461200190186699/40000000000000000)
  q := (167952374201736130147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14104]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14104]

theorem width_14105 : mW 14105 = 333277363294082 := by
  have hu : mW 14105 ≤ 333277363294082 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14105 ≤ 333277363294081 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14105 : RowArithmetic 14105 (140069305007792154327/125000000000000000000000) (608135116571344420775827/1000000000000000000000000) (7173960230974509/1000000000000000000000000) where
  r0 := (596953309501/1000000000000000000)
  k0 := (3652657452779737/1000000000000000000)
  k6 := (5764798013471239/500000000000000000)
  q := (167958328165054084049/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14105]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14105]

theorem width_14106 : mW 14106 = 333360069720815 := by
  have hu : mW 14106 ≤ 333360069720815 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14106 ≤ 333360069720814 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14106 : RowArithmetic 14106 (1120523779059292275629/1000000000000000000000000) (152030978293571008552309/250000000000000000000000) (143452726045239/20000000000000000000000) where
  r0 := (596889831967/1000000000000000000)
  k0 := (1826231621705093/500000000000000000)
  k6 := (1152918734268143/100000000000000000)
  q := (8398214095865858551/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14106]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14106]

theorem width_14107 : mW 14107 = 333442790806869 := by
  have hu : mW 14107 ≤ 333442790806869 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14107 ≤ 333442790806868 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14107 : RowArithmetic 14107 (560246562667808497727/500000000000000000000000) (608112711361391411555407/1000000000000000000000000) (1434262543007663/200000000000000000000000) where
  r0 := (298413182841/500000000000000000)
  k0 := (913067264533147/250000000000000000)
  k6 := (11528778701876627/1000000000000000000)
  q := (167970235458547833757/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14107]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14107]

theorem width_14108 : mW 14108 = 333525526553804 := by
  have hu : mW 14108 ≤ 333525526553804 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14108 ≤ 333525526553803 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14108 : RowArithmetic 14108 (140057809861131073/125000000000000000000) (608101511132308730675763/1000000000000000000000000) (1433997893838101/200000000000000000000000) where
  r0 := (149190727661/250000000000000000)
  k0 := (3652074896944667/1000000000000000000)
  k6 := (11528370104520369/1000000000000000000)
  q := (167976188788768510981/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14108]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14108]

theorem width_14109 : mW 14109 = 333608276963178 := by
  have hu : mW 14109 ≤ 333608276963178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14109 ≤ 333608276963177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14109 : RowArithmetic 14109 (224086367943465250113/200000000000000000000000) (304045156243339105479037/500000000000000000000000) (716866656460551/100000000000000000000000) where
  r0 := (18646858339/31250000000000000)
  k0 := (730376151966993/200000000000000000)
  k6 := (11527961550604957/1000000000000000000)
  q := (33596428381600327487/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14109]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14109]

theorem width_14110 : mW 14110 = 333691042036551 := by
  have hu : mW 14110 ≤ 333691042036551 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14110 ≤ 333691042036550 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14110 : RowArithmetic 14110 (280100301954547245979/250000000000000000000000) (30403955771207109304951/50000000000000000000000) (286693760046813/40000000000000000000000) where
  r0 := (298318017147/500000000000000000)
  k0 := (1825843323403661/500000000000000000)
  k6 := (5763776520061347/500000000000000000)
  q := (167988094816269643889/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14110]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14110]

theorem width_14111 : mW 14111 = 333773821775481 := by
  have hu : mW 14111 ≤ 333773821775481 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14111 ≤ 333773821775480 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14111 : RowArithmetic 14111 (1120370583189377790359/1000000000000000000000000) (76008489993042888905701/125000000000000000000000) (3583010889386017/500000000000000000000000) where
  r0 := (298286306489/500000000000000000)
  k0 := (3651492557853337/1000000000000000000)
  k6 := (2305428914613177/200000000000000000)
  q := (167994047513594957137/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14111]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14111]

theorem width_14112 : mW 14112 = 333856616181527 := by
  have hu : mW 14112 ≤ 333856616181527 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14112 ≤ 333856616181526 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14112 : RowArithmetic 14112 (1120339965828634014497/1000000000000000000000000) (608056726046923546775367/1000000000000000000000000) (1791174974324437/250000000000000000000000) where
  r0 := (596509202897/1000000000000000000)
  k0 := (3651298492967667/1000000000000000000)
  k6 := (2881684037356709/250000000000000000)
  q := 168
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14112]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14112]

theorem width_14113 : mW 14113 = 333939425256249 := by
  have hu : mW 14113 ≤ 333939425256249 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14113 ≤ 333939425256248 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14113 : RowArithmetic 14113 (1120309355733699339921/1000000000000000000000000) (608045533731526120955227/1000000000000000000000000) (7163378356634601/1000000000000000000000000) where
  r0 := (37277862753/62500000000000000)
  k0 := (456388056518121/125000000000000000)
  k6 := (5763163884598929/500000000000000000)
  q := (168005952275507191329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14113]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14113]

theorem width_14114 : mW 14114 = 334022249001206 := by
  have hu : mW 14114 ≤ 334022249001206 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14114 ≤ 334022249001205 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14114 : RowArithmetic 14114 (112027875290231690663/100000000000000000000000) (76004292874724206119419/125000000000000000000000) (7162057156669797/1000000000000000000000000) where
  r0 := (149095604107/250000000000000000)
  k0 := (1825455217689947/500000000000000000)
  k6 := (11525919432371259/1000000000000000000)
  q := (168011904340138946001/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14114]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14114]

theorem width_14115 : mW 14115 = 334105087417957 := by
  have hu : mW 14115 ≤ 334105087417957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14115 ≤ 334105087417956 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14115 : RowArithmetic 14115 (224049631466446150257/200000000000000000000000) (304011576922684516601929/500000000000000000000000) (3580368148645293/500000000000000000000000) where
  r0 := (149079760009/250000000000000000)
  k0 := (3650716442673219/1000000000000000000)
  k6 := (11525511138939353/1000000000000000000)
  q := (42004464048479418731/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14115]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14115]

theorem width_14116 : mW 14116 = 334187940508061 := by
  have hu : mW 14116 ≤ 334187940508061 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14116 ≤ 334187940508060 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14116 : RowArithmetic 14116 (560108784510592903373/500000000000000000000000) (60801196627389518357773/100000000000000000000000) (1431883155676853/200000000000000000000000) where
  r0 := (596255674867/1000000000000000000)
  k0 := (1825261237006737/500000000000000000)
  k6 := (5762551444447227/500000000000000000)
  q := (168023807836865785037/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14116]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14116]

theorem width_14117 : mW 14117 = 334270808273079 := by
  have hu : mW 14117 ≤ 334270808273079 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14117 ≤ 334270808273078 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14117 : RowArithmetic 14117 (1120186987966926786273/1000000000000000000000000) (38000048767688459850523/62500000000000000000000) (1431619119967627/200000000000000000000000) where
  r0 := (14904808023/25000000000000000)
  k0 := (365032852940143/100000000000000000)
  k6 := (11524694682228879/1000000000000000000)
  q := (168029759269005679309/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14117]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14117]

theorem width_14118 : mW 14118 = 334353690714568 := by
  have hu : mW 14118 ≤ 334353690714568 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14118 ≤ 334353690714567 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14118 : RowArithmetic 14118 (224031282833440306003/200000000000000000000000) (607989595872372641220259/1000000000000000000000000) (1789193940384907/250000000000000000000000) where
  r0 := (596128978191/1000000000000000000)
  k0 := (1825067304414337/500000000000000000)
  k6 := (11524286518934947/1000000000000000000)
  q := (21004463811294969593/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14118]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14118]

theorem width_14119 : mW 14119 = 334436587834089 := by
  have hu : mW 14119 ≤ 334436587834089 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14119 ≤ 334436587834088 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14119 : RowArithmetic 14119 (1120125847619756542257/1000000000000000000000000) (7599730163020130817681/12500000000000000000000) (357772813168807/50000000000000000000000) where
  r0 := (298032823339/500000000000000000)
  k0 := (1824970356146457/500000000000000000)
  k6 := (720242399937811/62500000000000000)
  q := (84020830750475206189/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14119]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14119]

theorem width_14120 : mW 14120 = 334519499633201 := by
  have hu : mW 14120 ≤ 334519499633201 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14120 ≤ 334519499633200 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14120 : RowArithmetic 14120 (1120095288322340337449/1000000000000000000000000) (607967231790372207753871/1000000000000000000000000) (7154137105235153/1000000000000000000000000) where
  r0 := (298001163189/500000000000000000)
  k0 := (912436709947199/250000000000000000)
  k6 := (11523470322431289/1000000000000000000)
  q := (168047612300800037283/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14120]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14120]

theorem width_14121 : mW 14121 = 334602426113464 := by
  have hu : mW 14121 ≤ 334602426113464 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14121 ≤ 334602426113463 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14121 : RowArithmetic 14121 (560032368136350883597/500000000000000000000000) (75994506514787681213317/125000000000000000000000) (447051142937761/62500000000000000000000) where
  r0 := (74492377161/125000000000000000)
  k0 := (912388247827741/250000000000000000)
  k6 := (11523062289206211/1000000000000000000)
  q := (33610712577986203713/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14121]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14121]

theorem width_14122 : mW 14122 = 334685367276437 := by
  have hu : mW 14122 ≤ 334685367276437 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14122 ≤ 334685367276436 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14122 : RowArithmetic 14122 (1120034191468591133983/1000000000000000000000000) (607944874025041848556443/1000000000000000000000000) (1430299961714157/200000000000000000000000) where
  r0 := (119175143881/200000000000000000)
  k0 := (3649359166854059/1000000000000000000)
  k6 := (11522654299322067/1000000000000000000)
  q := (21007439158545717421/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14122]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14122]

theorem width_14123 : mW 14123 = 334768323123680 := by
  have hu : mW 14123 ≤ 334768323123680 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14123 ≤ 334768323123679 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14123 : RowArithmetic 14123 (1120003653907759077/1000000000000000000000) (607933697510237161644201/1000000000000000000000000) (893772708727823/125000000000000000000000) where
  r0 := (595812432727/1000000000000000000)
  k0 := (729833073283157/200000000000000000)
  k6 := (5761123176385593/500000000000000000)
  q := (84032731718063289437/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14123]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14123]

theorem width_14124 : mW 14124 = 334851293656753 := by
  have hu : mW 14124 ≤ 334851293656753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14124 ≤ 334851293656752 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14124 : RowArithmetic 14124 (1119973123587957128879/1000000000000000000000000) (303961261286765637806727/500000000000000000000000) (357443193532361/50000000000000000000000) where
  r0 := (2382996629/4000000000000000)
  k0 := (3648971589987719/1000000000000000000)
  k6 := (1440229806193237/125000000000000000)
  q := (168071413393235912301/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14124]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14124]

theorem width_14125 : mW 14125 = 334934278877216 := by
  have hu : mW 14125 ≤ 334934278877216 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14125 ≤ 334934278877215 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14125 : RowArithmetic 14125 (559971300253468857621/500000000000000000000000) (121582269842913649041/200000000000000000000) (7147546410932389/1000000000000000000000000) where
  r0 := (595685892973/1000000000000000000)
  k0 := (3648777837570623/1000000000000000000)
  k6 := (11521430589638529/1000000000000000000)
  q := (16807736313971611091/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14125]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14125]

theorem width_14126 : mW 14126 = 335017278786628 := by
  have hu : mW 14126 ≤ 335017278786628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14126 ≤ 335017278786627 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14126 : RowArithmetic 14126 (559956042331227354923/500000000000000000000000) (151975044358248016865511/250000000000000000000000) (7146229290565853/1000000000000000000000000) where
  r0 := (148905659973/250000000000000000)
  k0 := (3648584109156071/1000000000000000000)
  k6 := (11521022773041419/1000000000000000000)
  q := (84041656337794771/500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14126]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14126]

theorem width_14127 : mW 14127 = 335100293386550 := by
  have hu : mW 14127 ≤ 335100293386550 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14127 ≤ 335100293386549 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14127 : RowArithmetic 14127 (223976315210452353371/200000000000000000000000) (607889007228447001300311/1000000000000000000000000) (7144912509435379/1000000000000000000000000) where
  r0 := (148889849501/250000000000000000)
  k0 := (1824195202369349/500000000000000000)
  k6 := (5760307499873451/500000000000000000)
  q := (10505578875054910557/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14127]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14127]

theorem width_14128 : mW 14128 = 335183322678541 := by
  have hu : mW 14128 ≤ 335183322678541 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14128 ≤ 335183322678540 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14128 : RowArithmetic 14128 (1119851074674114543259/1000000000000000000000000) (607877838600577425171517/1000000000000000000000000) (7143596067428823/1000000000000000000000000) where
  r0 := (595496167307/1000000000000000000)
  k0 := (18240983621581/5000000000000000)
  k6 := (5760103634873657/500000000000000000)
  q := (168095211115605551031/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14128]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14128]

theorem width_14129 : mW 14129 = 335266366664161 := by
  have hu : mW 14129 ≤ 335266366664161 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14129 ≤ 335266366664160 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14129 : RowArithmetic 14129 (1119820580525769031373/1000000000000000000000000) (303933335774513848416921/500000000000000000000000) (1428455992886813/200000000000000000000000) where
  r0 := (595432947797/1000000000000000000)
  k0 := (1824001533940073/500000000000000000)
  k6 := (2303959916606999/200000000000000000)
  q := (33620232003958568757/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14129]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14129]

theorem width_14130 : mW 14130 = 335349425344971 := by
  have hu : mW 14130 ≤ 335349425344971 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14130 ≤ 335349425344970 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14130 : RowArithmetic 14130 (44791603744199262381/40000000000000000000000) (121571101214688478198439/200000000000000000000000) (7140964200339013/1000000000000000000000000) where
  r0 := (595369739473/1000000000000000000)
  k0 := (3647809435431291/1000000000000000000)
  k6 := (5759695969801143/500000000000000000)
  q := (42026777178365699661/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14130]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14130]

theorem width_14131 : mW 14131 = 335432498722531 := by
  have hu : mW 14131 ≤ 335432498722531 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14131 ≤ 335432498722530 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14131 : RowArithmetic 14131 (34992487934672184427/31250000000000000000000) (151961085543366535120889/250000000000000000000000) (7139648775031639/1000000000000000000000000) where
  r0 := (148826635583/250000000000000000)
  k0 := (1823807913482133/500000000000000000)
  k6 := (1151898433944153/100000000000000000)
  q := (84056528598318881563/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14131]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14131]

theorem width_14132 : mW 14132 = 335515586798401 := by
  have hu : mW 14132 ≤ 335515586798401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14132 ≤ 335515586798400 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14132 : RowArithmetic 14132 (111972914143711272153/100000000000000000000000) (60783317984874374599083/100000000000000000000000) (7138333688399963/1000000000000000000000000) where
  r0 := (59524335637/100000000000000000)
  k0 := (3647422242470633/1000000000000000000)
  k6 := (11518576782545071/1000000000000000000)
  q := (33623801093868016159/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14132]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14132]

theorem width_14133 : mW 14133 = 335598689574140 := by
  have hu : mW 14133 ≤ 335598689574140 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14133 ≤ 335598689574139 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14133 : RowArithmetic 14133 (223939735237110025239/200000000000000000000000) (303911009549460020412013/500000000000000000000000) (285480757613283/40000000000000000000000) where
  r0 := (37198761349/62500000000000000)
  k0 := (3647228681945019/1000000000000000000)
  k6 := (5759084634452629/500000000000000000)
  q := (168124953531592091263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14133]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14133]

theorem width_14134 : mW 14134 = 335681807051310 := by
  have hu : mW 14134 ≤ 335681807051310 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14134 ≤ 335681807051309 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14134 : RowArithmetic 14134 (559834109076290724687/500000000000000000000000) (607810859923640056159567/1000000000000000000000000) (3567852265358021/500000000000000000000000) where
  r0 := (595117017973/1000000000000000000)
  k0 := (227939696586761/62500000000000000)
  k6 := (5758880899257219/500000000000000000)
  q := (168130901383416130189/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14134]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14134]

theorem width_14135 : mW 14135 = 335764939231471 := by
  have hu : mW 14135 ≤ 335764939231471 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14135 ≤ 335764939231470 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14135 : RowArithmetic 14135 (559818883667984011061/500000000000000000000000) (303899851161274412985863/500000000000000000000000) (3567195229720013/500000000000000000000000) where
  r0 := (595053865533/1000000000000000000)
  k0 := (1823420816395831/500000000000000000)
  k6 := (11517354371364961/1000000000000000000)
  q := (168136849024834529281/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14135]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14135]

theorem width_14136 : mW 14136 = 335848086116183 := by
  have hu : mW 14136 ≤ 335848086116183 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14136 ≤ 335848086116182 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14136 : RowArithmetic 14136 (55980366186673603173/50000000000000000000000) (607788546295291631129043/1000000000000000000000000) (713307672639223/100000000000000000000000) where
  r0 := (297495362131/500000000000000000)
  k0 := (1823324072076581/500000000000000000)
  k6 := (5758473493724591/500000000000000000)
  q := (1681427964558696163/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14136]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14136]

theorem width_14137 : mW 14137 = 335931247707006 := by
  have hu : mW 14137 ≤ 335931247707006 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14137 ≤ 335931247707005 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14137 : RowArithmetic 14137 (559788443671428339961/500000000000000000000000) (607777391841513712010473/1000000000000000000000000) (1782940832865227/250000000000000000000000) where
  r0 := (148731898539/250000000000000000)
  k0 := (3646454679464233/1000000000000000000)
  k6 := (11516539646759453/1000000000000000000)
  q := (10509296479783982191/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14137]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14137]

theorem width_14138 : mW 14138 = 336014424005502 := by
  have hu : mW 14138 ≤ 336014424005502 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14138 ≤ 336014424005501 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14138 : RowArithmetic 14138 (1119546458161884759371/1000000000000000000000000) (607766238960860484941037/1000000000000000000000000) (7130450274534313/1000000000000000000000000) where
  r0 := (594864475213/1000000000000000000)
  k0 := (3646261238722557/1000000000000000000)
  k6 := (11516132349288131/1000000000000000000)
  q := (42038672671719786353/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14138]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14138]

theorem width_14139 : mW 14139 = 336097615013230 := by
  have hu : mW 14139 ≤ 336097615013230 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14139 ≤ 336097615013229 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14139 : RowArithmetic 14139 (1119516036188321736001/1000000000000000000000000) (607755087652977521030787/1000000000000000000000000) (7129137555500813/1000000000000000000000000) where
  r0 := (594801367431/1000000000000000000)
  k0 := (729213564385163/200000000000000000)
  k6 := (5757862547513787/500000000000000000)
  q := (42040159371724555821/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14139]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14139]

theorem width_14140 : mW 14140 = 336180820731752 := by
  have hu : mW 14140 ≤ 336180820731752 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14140 ≤ 336180820731751 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14140 : RowArithmetic 14140 (559742810709966136011/500000000000000000000000) (607743937917510466629047/1000000000000000000000000) (7127825174248753/1000000000000000000000000) where
  r0 := (297369135403/500000000000000000)
  k0 := (3645874429065557/1000000000000000000)
  k6 := (11515317883970143/1000000000000000000)
  q := (84083292038311630321/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14140]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14140]

theorem width_14141 : mW 14141 = 336264041162627 := by
  have hu : mW 14141 ≤ 336264041162627 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14141 ≤ 336264041162626 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14141 : RowArithmetic 14141 (1119455213854483573697/1000000000000000000000000) (151933197438526253814429/250000000000000000000000) (7126513130666593/1000000000000000000000000) where
  r0 := (74334398167/125000000000000000)
  k0 := (455710132517433/125000000000000000)
  k6 := (11514910716108199/1000000000000000000)
  q := (168172530456076565513/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14141]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14141]

theorem width_14142 : mW 14142 = 336347276307418 := by
  have hu : mW 14142 ≤ 336347276307418 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14142 ≤ 336347276307417 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14142 : RowArithmetic 14142 (1119424813489741523809/1000000000000000000000000) (151930410790601773707379/250000000000000000000000) (28500805698571/4000000000000000000000) where
  r0 := (297306055509/500000000000000000)
  k0 := (1822743857571073/500000000000000000)
  k6 := (5757251795717053/500000000000000000)
  q := (168178476625280441979/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14142]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14142]

theorem width_14143 : mW 14143 = 336430526167684 := by
  have hu : mW 14143 ≤ 336430526167684 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14143 ≤ 336430526167683 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14143 : RowArithmetic 14143 (27984860508086877489/25000000000000000000000) (151927624535515656486473/250000000000000000000000) (445243128504111/62500000000000000000000) where
  r0 := (594549047849/1000000000000000000)
  k0 := (729058878813643/200000000000000000)
  k6 := (1151409650994023/100000000000000000)
  q := (84092211292128595089/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14143]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14143]

theorem width_14144 : mW 14144 = 336513790744986 := by
  have hu : mW 14144 ≤ 336513790744986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14144 ≤ 336513790744985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14144 : RowArithmetic 14144 (69960252147090816161/62500000000000000000000) (18990604834147429606073/31250000000000000000000) (7122579024824223/1000000000000000000000000) where
  r0 := (297242997913/500000000000000000)
  k0 := (91127527422807/25000000000000000)
  k6 := (5756844735809469/500000000000000000)
  q := (42047592083257276577/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14144]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14144]

theorem width_14145 : mW 14145 = 336597070040886 := by
  have hu : mW 14145 ≤ 336597070040886 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14145 ≤ 336597070040885 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14145 : RowArithmetic 14145 (559666827788722246003/500000000000000000000000) (151922053203504644248599/250000000000000000000000) (712126833080667/100000000000000000000000) where
  r0 := (594422954947/1000000000000000000)
  k0 := (3644907823672013/1000000000000000000)
  k6 := (11513282476462601/1000000000000000000)
  q := (1345570510972947861/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14145]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14145]

theorem width_14146 : mW 14146 = 336680364056944 := by
  have hu : mW 14146 ≤ 336680364056944 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14146 ≤ 336680364056943 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14146 : RowArithmetic 14146 (1119303283993220478329/1000000000000000000000000) (9494954257900178344557/15625000000000000000000) (1423991594780357/200000000000000000000000) where
  r0 := (594359925209/1000000000000000000)
  k0 := (3644714574342023/1000000000000000000)
  k6 := (2878218881115897/250000000000000000)
  q := (168202259200047607447/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14146]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14146]

theorem width_14147 : mW 14147 = 336763672794722 := by
  have hu : mW 14147 ≤ 336763672794722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14147 ≤ 336763672794721 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14147 : RowArithmetic 14147 (1119272919598551877367/1000000000000000000000000) (607665933767142733142869/1000000000000000000000000) (7118647953998237/1000000000000000000000000) where
  r0 := (594296906609/1000000000000000000)
  k0 := (3644521348916913/1000000000000000000)
  k6 := (460498744624571/40000000000000000)
  q := (3364164086366775303/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14147]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14147]

theorem width_14148 : mW 14148 = 336846996255780 := by
  have hu : mW 14148 ≤ 336846996255780 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14148 ≤ 336846996255779 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14148 : RowArithmetic 14148 (1119242562391211534459/1000000000000000000000000) (37978424787391187142423/62500000000000000000000) (3558669135492393/500000000000000000000000) where
  r0 := (74279237393/125000000000000000)
  k0 := (1822164073695643/500000000000000000)
  k6 := (2302412349981407/200000000000000000)
  q := (84107074613257118087/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14148]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14148]

theorem width_14149 : mW 14149 = 336930334441679 := by
  have hu : mW 14149 ≤ 336930334441679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14149 ≤ 336930334441678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14149 : RowArithmetic 14149 (1119212212368972626653/1000000000000000000000000) (121528732199721366438737/200000000000000000000000) (889503615593777/125000000000000000000000) where
  r0 := (594170902813/1000000000000000000)
  k0 := (1822067484882939/500000000000000000)
  k6 := (2302330985466849/200000000000000000)
  q := (168220093924596297023/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14149]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14149]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14075 then ⟨(1121477666316462770833/1000000000000000000000000), (304235978450427757088357/500000000000000000000000), (1442767489484229/200000000000000000000000)⟩ else
  if n = 14076 then ⟨(1121446785876102430851/1000000000000000000000000), (608460705811791933913977/1000000000000000000000000), (7212503221233977/1000000000000000000000000)⟩ else
  if n = 14077 then ⟨(1121415912783382642037/1000000000000000000000000), (608449456317684495331329/1000000000000000000000000), (1802792334987331/250000000000000000000000)⟩ else
  if n = 14078 then ⟨(280346261759003635717/250000000000000000000000), (152109552104543000549367/250000000000000000000000), (1441967160690543/200000000000000000000000)⟩ else
  if n = 14079 then ⟨(112135418863171131729/100000000000000000000000), (304213481056446659532051/500000000000000000000000), (3604251305814883/500000000000000000000000)⟩ else
  if n = 14080 then ⟨(560661668784092963421/500000000000000000000000), (608415717401487438968861/1000000000000000000000000), (72071697643661/10000000000000000000000)⟩ else
  if n = 14081 then ⟨(560646246921576122297/500000000000000000000000), (152101118570898370676709/250000000000000000000000), (7205837261547387/1000000000000000000000000)⟩ else
  if n = 14082 then ⟨(280315414363581405119/250000000000000000000000), (304196616379425310316799/500000000000000000000000), (1440901020611873/200000000000000000000000)⟩ else
  if n = 14083 then ⟨(1121230828399422314073/1000000000000000000000000), (608381992826898223231659/1000000000000000000000000), (7203173288787821/1000000000000000000000000)⟩ else
  if n = 14084 then ⟨(1121200006676158928831/1000000000000000000000000), (608370754487375713749969/1000000000000000000000000), (3600920909309283/500000000000000000000000)⟩ else
  if n = 14085 then ⟨(280292298070563244463/250000000000000000000000), (608359517739922649199223/1000000000000000000000000), (7200510692437461/1000000000000000000000000)⟩ else
  if n = 14086 then ⟨(1121138385215423448289/1000000000000000000000000), (38021767661511168529281/62500000000000000000000), (7199179910130433/1000000000000000000000000)⟩ else
  if n = 14087 then ⟨(560553792736694835227/500000000000000000000000), (608337049019783666973509/1000000000000000000000000), (7197849471583437/1000000000000000000000000)⟩ else
  if n = 14088 then ⟨(224215358610774489461/200000000000000000000000), (304162908523188685374333/500000000000000000000000), (14055701907583/1953125000000000000000)⟩ else
  if n = 14089 then ⟨(1121046007954592360333/1000000000000000000000000), (608314586663599842118267/1000000000000000000000000), (3597594812656819/500000000000000000000000)⟩ else
  if n = 14090 then ⟨(56050761508663601357/50000000000000000000000), (1520758394677728022947/2500000000000000000000), (359693010868149/50000000000000000000000)⟩ else
  if n = 14091 then ⟨(22419689194152688151/20000000000000000000000), (608292130668491687437287/1000000000000000000000000), (3596265576358333/500000000000000000000000)⟩ else
  if n = 14092 then ⟨(1120953696555403367779/1000000000000000000000000), (304140452527720796308747/500000000000000000000000), (3595601215630443/500000000000000000000000)⟩ else
  if n = 14093 then ⟨(1120922940714303116733/1000000000000000000000000), (304134840515790683858787/500000000000000000000000), (3594937026440929/500000000000000000000000)⟩ else
  if n = 14094 then ⟨(560446096091029947849/500000000000000000000000), (304129229298275808827471/500000000000000000000000), (7188546017465887/1000000000000000000000000)⟩ else
  if n = 14095 then ⟨(224172290191279944899/200000000000000000000000), (304123618874996486474073/500000000000000000000000), (3593609162449643/500000000000000000000000)⟩ else
  if n = 14096 then ⟨(560415358517525326729/500000000000000000000000), (304118009245773112189813/500000000000000000000000), (3592945487534227/500000000000000000000000)⟩ else
  if n = 14097 then ⟨(560399995207869974581/500000000000000000000000), (608224800820852228196641/1000000000000000000000000), (112258811997809/15625000000000000000000)⟩ else
  if n = 14098 then ⟨(140096158887024753987/125000000000000000000000), (304106792368776033735487/500000000000000000000000), (7183237303159769/1000000000000000000000000)⟩ else
  if n = 14099 then ⟨(1120738559074153975891/1000000000000000000000000), (608202370241286758861403/1000000000000000000000000), (718191098085491/100000000000000000000000)⟩ else
  if n = 14100 then ⟨(35022120448354322547/31250000000000000000000), (608191157331697614031021/1000000000000000000000000), (3590292500415873/500000000000000000000000)⟩ else
  if n = 14101 then ⟨(1120677156913483634963/1000000000000000000000000), (608179946008425924300703/1000000000000000000000000), (3589629681488457/500000000000000000000000)⟩ else
  if n = 14102 then ⟨(140080808346290282629/125000000000000000000000), (76021092033889142441113/125000000000000000000000), (1435586813435411/200000000000000000000000)⟩ else
  if n = 14103 then ⟨(1120615783915588007587/1000000000000000000000000), (152039382029850209977689/250000000000000000000000), (7176609113318877/1000000000000000000000000)⟩ else
  if n = 14104 then ⟨(1120585108347014461971/1000000000000000000000000), (24325852862117227514047/40000000000000000000000), (3587642250644547/500000000000000000000000)⟩ else
  if n = 14105 then ⟨(140069305007792154327/125000000000000000000000), (608135116571344420775827/1000000000000000000000000), (7173960230974509/1000000000000000000000000)⟩ else
  if n = 14106 then ⟨(1120523779059292275629/1000000000000000000000000), (152030978293571008552309/250000000000000000000000), (143452726045239/20000000000000000000000)⟩ else
  if n = 14107 then ⟨(560246562667808497727/500000000000000000000000), (608112711361391411555407/1000000000000000000000000), (1434262543007663/200000000000000000000000)⟩ else
  if n = 14108 then ⟨(140057809861131073/125000000000000000000), (608101511132308730675763/1000000000000000000000000), (1433997893838101/200000000000000000000000)⟩ else
  if n = 14109 then ⟨(224086367943465250113/200000000000000000000000), (304045156243339105479037/500000000000000000000000), (716866656460551/100000000000000000000000)⟩ else
  if n = 14110 then ⟨(280100301954547245979/250000000000000000000000), (30403955771207109304951/50000000000000000000000), (286693760046813/40000000000000000000000)⟩ else
  if n = 14111 then ⟨(1120370583189377790359/1000000000000000000000000), (76008489993042888905701/125000000000000000000000), (3583010889386017/500000000000000000000000)⟩ else
  if n = 14112 then ⟨(1120339965828634014497/1000000000000000000000000), (608056726046923546775367/1000000000000000000000000), (1791174974324437/250000000000000000000000)⟩ else
  if n = 14113 then ⟨(1120309355733699339921/1000000000000000000000000), (608045533731526120955227/1000000000000000000000000), (7163378356634601/1000000000000000000000000)⟩ else
  if n = 14114 then ⟨(112027875290231690663/100000000000000000000000), (76004292874724206119419/125000000000000000000000), (7162057156669797/1000000000000000000000000)⟩ else
  if n = 14115 then ⟨(224049631466446150257/200000000000000000000000), (304011576922684516601929/500000000000000000000000), (3580368148645293/500000000000000000000000)⟩ else
  if n = 14116 then ⟨(560108784510592903373/500000000000000000000000), (60801196627389518357773/100000000000000000000000), (1431883155676853/200000000000000000000000)⟩ else
  if n = 14117 then ⟨(1120186987966926786273/1000000000000000000000000), (38000048767688459850523/62500000000000000000000), (1431619119967627/200000000000000000000000)⟩ else
  if n = 14118 then ⟨(224031282833440306003/200000000000000000000000), (607989595872372641220259/1000000000000000000000000), (1789193940384907/250000000000000000000000)⟩ else
  if n = 14119 then ⟨(1120125847619756542257/1000000000000000000000000), (7599730163020130817681/12500000000000000000000), (357772813168807/50000000000000000000000)⟩ else
  if n = 14120 then ⟨(1120095288322340337449/1000000000000000000000000), (607967231790372207753871/1000000000000000000000000), (7154137105235153/1000000000000000000000000)⟩ else
  if n = 14121 then ⟨(560032368136350883597/500000000000000000000000), (75994506514787681213317/125000000000000000000000), (447051142937761/62500000000000000000000)⟩ else
  if n = 14122 then ⟨(1120034191468591133983/1000000000000000000000000), (607944874025041848556443/1000000000000000000000000), (1430299961714157/200000000000000000000000)⟩ else
  if n = 14123 then ⟨(1120003653907759077/1000000000000000000000), (607933697510237161644201/1000000000000000000000000), (893772708727823/125000000000000000000000)⟩ else
  if n = 14124 then ⟨(1119973123587957128879/1000000000000000000000000), (303961261286765637806727/500000000000000000000000), (357443193532361/50000000000000000000000)⟩ else
  if n = 14125 then ⟨(559971300253468857621/500000000000000000000000), (121582269842913649041/200000000000000000000), (7147546410932389/1000000000000000000000000)⟩ else
  if n = 14126 then ⟨(559956042331227354923/500000000000000000000000), (151975044358248016865511/250000000000000000000000), (7146229290565853/1000000000000000000000000)⟩ else
  if n = 14127 then ⟨(223976315210452353371/200000000000000000000000), (607889007228447001300311/1000000000000000000000000), (7144912509435379/1000000000000000000000000)⟩ else
  if n = 14128 then ⟨(1119851074674114543259/1000000000000000000000000), (607877838600577425171517/1000000000000000000000000), (7143596067428823/1000000000000000000000000)⟩ else
  if n = 14129 then ⟨(1119820580525769031373/1000000000000000000000000), (303933335774513848416921/500000000000000000000000), (1428455992886813/200000000000000000000000)⟩ else
  if n = 14130 then ⟨(44791603744199262381/40000000000000000000000), (121571101214688478198439/200000000000000000000000), (7140964200339013/1000000000000000000000000)⟩ else
  if n = 14131 then ⟨(34992487934672184427/31250000000000000000000), (151961085543366535120889/250000000000000000000000), (7139648775031639/1000000000000000000000000)⟩ else
  if n = 14132 then ⟨(111972914143711272153/100000000000000000000000), (60783317984874374599083/100000000000000000000000), (7138333688399963/1000000000000000000000000)⟩ else
  if n = 14133 then ⟨(223939735237110025239/200000000000000000000000), (303911009549460020412013/500000000000000000000000), (285480757613283/40000000000000000000000)⟩ else
  if n = 14134 then ⟨(559834109076290724687/500000000000000000000000), (607810859923640056159567/1000000000000000000000000), (3567852265358021/500000000000000000000000)⟩ else
  if n = 14135 then ⟨(559818883667984011061/500000000000000000000000), (303899851161274412985863/500000000000000000000000), (3567195229720013/500000000000000000000000)⟩ else
  if n = 14136 then ⟨(55980366186673603173/50000000000000000000000), (607788546295291631129043/1000000000000000000000000), (713307672639223/100000000000000000000000)⟩ else
  if n = 14137 then ⟨(559788443671428339961/500000000000000000000000), (607777391841513712010473/1000000000000000000000000), (1782940832865227/250000000000000000000000)⟩ else
  if n = 14138 then ⟨(1119546458161884759371/1000000000000000000000000), (607766238960860484941037/1000000000000000000000000), (7130450274534313/1000000000000000000000000)⟩ else
  if n = 14139 then ⟨(1119516036188321736001/1000000000000000000000000), (607755087652977521030787/1000000000000000000000000), (7129137555500813/1000000000000000000000000)⟩ else
  if n = 14140 then ⟨(559742810709966136011/500000000000000000000000), (607743937917510466629047/1000000000000000000000000), (7127825174248753/1000000000000000000000000)⟩ else
  if n = 14141 then ⟨(1119455213854483573697/1000000000000000000000000), (151933197438526253814429/250000000000000000000000), (7126513130666593/1000000000000000000000000)⟩ else
  if n = 14142 then ⟨(1119424813489741523809/1000000000000000000000000), (151930410790601773707379/250000000000000000000000), (28500805698571/4000000000000000000000)⟩ else
  if n = 14143 then ⟨(27984860508086877489/25000000000000000000000), (151927624535515656486473/250000000000000000000000), (445243128504111/62500000000000000000000)⟩ else
  if n = 14144 then ⟨(69960252147090816161/62500000000000000000000), (18990604834147429606073/31250000000000000000000), (7122579024824223/1000000000000000000000000)⟩ else
  if n = 14145 then ⟨(559666827788722246003/500000000000000000000000), (151922053203504644248599/250000000000000000000000), (712126833080667/100000000000000000000000)⟩ else
  if n = 14146 then ⟨(1119303283993220478329/1000000000000000000000000), (9494954257900178344557/15625000000000000000000), (1423991594780357/200000000000000000000000)⟩ else
  if n = 14147 then ⟨(1119272919598551877367/1000000000000000000000000), (607665933767142733142869/1000000000000000000000000), (7118647953998237/1000000000000000000000000)⟩ else
  if n = 14148 then ⟨(1119242562391211534459/1000000000000000000000000), (37978424787391187142423/62500000000000000000000), (3558669135492393/500000000000000000000000)⟩ else
  ⟨(1119212212368972626653/1000000000000000000000000), (121528732199721366438737/200000000000000000000000), (889503615593777/125000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14075 ≤ n) (hb : n ≤ 14149) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14075
  · exact row_14076
  · exact row_14077
  · exact row_14078
  · exact row_14079
  · exact row_14080
  · exact row_14081
  · exact row_14082
  · exact row_14083
  · exact row_14084
  · exact row_14085
  · exact row_14086
  · exact row_14087
  · exact row_14088
  · exact row_14089
  · exact row_14090
  · exact row_14091
  · exact row_14092
  · exact row_14093
  · exact row_14094
  · exact row_14095
  · exact row_14096
  · exact row_14097
  · exact row_14098
  · exact row_14099
  · exact row_14100
  · exact row_14101
  · exact row_14102
  · exact row_14103
  · exact row_14104
  · exact row_14105
  · exact row_14106
  · exact row_14107
  · exact row_14108
  · exact row_14109
  · exact row_14110
  · exact row_14111
  · exact row_14112
  · exact row_14113
  · exact row_14114
  · exact row_14115
  · exact row_14116
  · exact row_14117
  · exact row_14118
  · exact row_14119
  · exact row_14120
  · exact row_14121
  · exact row_14122
  · exact row_14123
  · exact row_14124
  · exact row_14125
  · exact row_14126
  · exact row_14127
  · exact row_14128
  · exact row_14129
  · exact row_14130
  · exact row_14131
  · exact row_14132
  · exact row_14133
  · exact row_14134
  · exact row_14135
  · exact row_14136
  · exact row_14137
  · exact row_14138
  · exact row_14139
  · exact row_14140
  · exact row_14141
  · exact row_14142
  · exact row_14143
  · exact row_14144
  · exact row_14145
  · exact row_14146
  · exact row_14147
  · exact row_14148
  · exact row_14149

end BstLean.Part271.R3.Rows14075
