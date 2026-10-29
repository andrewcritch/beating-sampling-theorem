import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14237–14311. -/
namespace BstLean.Part271.R3.Rows14237
open Real BstLean.Part130 BstLean.Part227

theorem width_14237 : mW 14237 = 344321940829262 := by
  have hu : mW 14237 ≤ 344321940829262 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14237 ≤ 344321940829261 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14237 : RowArithmetic 14237 (558284643956201136453/500000000000000000000000) (9479216126799341194693/15625000000000000000000) (7002112334951073/1000000000000000000000000) where
  r0 := (2943352499/5000000000000000)
  k0 := (906807093271841/250000000000000000)
  k6 := (11476022564906097/1000000000000000000)
  q := (168742407236592426183/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14237]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14237]

theorem width_14238 : mW 14238 = 344406595785083 := by
  have hu : mW 14238 ≤ 344406595785083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14238 ≤ 344406595785082 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14238 : RowArithmetic 14238 (1116539568547964702429/1000000000000000000000000) (303329417387494444108031/500000000000000000000000) (7000832521991881/1000000000000000000000000) where
  r0 := (147152120837/250000000000000000)
  k0 := (72540746075093/20000000000000000)
  k6 := (11475619550997001/1000000000000000000)
  q := (16874833332510279937/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14238]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14238]

theorem width_14239 : mW 14239 = 344491265606473 := by
  have hu : mW 14239 ≤ 344491265606473 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14239 ≤ 344491265606472 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14239 : RowArithmetic 14239 (1116509856171651264299/1000000000000000000000000) (75830979871586177845179/125000000000000000000000) (6999553035982809/1000000000000000000000000) where
  r0 := (73568309723/125000000000000000)
  k0 := (3626846257904021/1000000000000000000)
  k6 := (11475216579543941/1000000000000000000)
  q := (10547141200344290451/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14239]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14239]

theorem width_14240 : mW 14240 = 344575950294998 := by
  have hu : mW 14240 ≤ 344575950294998 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14240 ≤ 344575950294997 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14240 : RowArithmetic 14240 (55824007539065556659/50000000000000000000000) (606636844707915756174083/1000000000000000000000000) (6998273876816631/1000000000000000000000000) where
  r0 := (294242241553/500000000000000000)
  k0 := (145066209421321/40000000000000000)
  k6 := (11474813650539461/1000000000000000000)
  q := (168760184877831891999/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14240]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14240]

theorem width_14241 : mW 14241 = 344660649852224 := by
  have hu : mW 14241 ≤ 344660649852224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14241 ≤ 344660649852223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14241 : RowArithmetic 14241 (1116450452374794330539/1000000000000000000000000) (606625851980324401928559/1000000000000000000000000) (6996995044386169/1000000000000000000000000) where
  r0 := (588422499311/1000000000000000000)
  k0 := (113327007394879/31250000000000000)
  k6 := (1147441076397611/100000000000000000)
  q := (42191527585523613037/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14241]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14241]

theorem width_14242 : mW 14242 = 344745364279718 := by
  have hu : mW 14242 ≤ 344745364279718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14242 ≤ 344745364279717 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14242 : RowArithmetic 14242 (1116420760949951194469/1000000000000000000000000) (606614860789571967873727/1000000000000000000000000) (3497858269292133/500000000000000000000000) where
  r0 := (147090131599/250000000000000000)
  k0 := (3626273261207793/1000000000000000000)
  k6 := (5737003959923219/500000000000000000)
  q := (42193008899579560561/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14242]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14242]

theorem width_14243 : mW 14243 = 344830093579046 := by
  have hu : mW 14243 ≤ 344830093579046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14243 ≤ 344830093579045 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14243 : RowArithmetic 14243 (1116391076504633439409/1000000000000000000000000) (606603871135315077301957/1000000000000000000000000) (699443835930383/100000000000000000000000) where
  r0 := (588298564359/1000000000000000000)
  k0 := (1813041154622783/500000000000000000)
  k6 := (11473605118142997/1000000000000000000)
  q := (168777960646525173021/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14243]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14243]

theorem width_14244 : mW 14244 = 344914837751774 := by
  have hu : mW 14244 ≤ 344914837751774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14244 ≤ 344914837751773 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14244 : RowArithmetic 14244 (558180699518346812657/500000000000000000000000) (606592883017210619136277/1000000000000000000000000) (3496580253218907/500000000000000000000000) where
  r0 := (147059153299/250000000000000000)
  k0 := (145035655229633/40000000000000000)
  k6 := (11473202358858339/1000000000000000000)
  q := (168783885486737151367/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14244]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14244]

theorem width_14245 : mW 14245 = 344999596799468 := by
  have hu : mW 14245 ≤ 344999596799468 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14245 ≤ 344999596799467 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14245 : RowArithmetic 14245 (558165864271992578611/500000000000000000000000) (303290948217457743740459/500000000000000000000000) (6991882979879213/1000000000000000000000000) where
  r0 := (294087336453/500000000000000000)
  k0 := (1812850237847097/500000000000000000)
  k6 := (11472799641985021/1000000000000000000)
  q := (168789810118976080327/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14245]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14245]

theorem width_14246 : mW 14246 = 345084370723696 := by
  have hu : mW 14246 ≤ 345084370723696 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14246 ≤ 345084370723695 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14246 : RowArithmetic 14246 (1116302065024361227057/1000000000000000000000000) (303285455694043309493469/500000000000000000000000) (6990605779521027/1000000000000000000000000) where
  r0 := (117622548697/200000000000000000)
  k0 := (72510191881941/20000000000000000)
  k6 := (28680992418789/2500000000000000)
  q := (1687957345432638591/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14246]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14246]

theorem width_14247 : mW 14247 = 345169159526023 := by
  have hu : mW 14247 ≤ 345169159526023 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14247 ≤ 345169159526022 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14247 : RowArithmetic 14247 (223254481695135491741/200000000000000000000000) (606559927876381237642707/1000000000000000000000000) (6989328905256361/1000000000000000000000000) where
  r0 := (588050824931/1000000000000000000)
  k0 := (3625318735946931/1000000000000000000)
  k6 := (5735997167721317/500000000000000000)
  q := (168801658759622383043/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14247]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14247]

theorem width_14248 : mW 14248 = 345253963208017 := by
  have hu : mW 14248 ≤ 345253963208017 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14248 ≤ 345253963208016 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14248 : RowArithmetic 14248 (1116242758895788733627/1000000000000000000000000) (151637236474864124391343/250000000000000000000000) (69880523569783/10000000000000000000000) where
  r0 := (293994458621/500000000000000000)
  k0 := (113285246913793/31250000000000000)
  k6 := (2294318349151737/200000000000000000)
  q := (16880758276807354367/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14248]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14248]

theorem width_14249 : mW 14249 = 345338781771244 := by
  have hu : mW 14249 ≤ 345338781771244 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14249 ≤ 345338781771243 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14249 : RowArithmetic 14249 (1116213116282551834851/1000000000000000000000000) (151634491364242433775227/250000000000000000000000) (3493388067290009/500000000000000000000000) where
  r0 := (293963510207/500000000000000000)
  k0 := (906234272492939/250000000000000000)
  k6 := (2294237839691263/200000000000000000)
  q := (33762701313727845731/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14249]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14249]

theorem width_14250 : mW 14250 = 345423615217270 := by
  have hu : mW 14250 ≤ 345423615217270 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14250 ≤ 345423615217269 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14250 : RowArithmetic 14250 (1116183480633824388349/1000000000000000000000000) (30326349327428920676321/50000000000000000000000) (698550023795473/100000000000000000000000) where
  r0 := (117573026889/200000000000000000)
  k0 := (3624746302135607/1000000000000000000)
  k6 := (11470786693528089/1000000000000000000)
  q := (21102428770167665229/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14250]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14250]

theorem width_14251 : mW 14251 = 345508463547662 := by
  have hu : mW 14251 ≤ 345508463547662 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14251 ≤ 345508463547661 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14251 : RowArithmetic 14251 (1116153851947464334793/1000000000000000000000000) (4852128073391520044341/8000000000000000000000) (3492112333497837/500000000000000000000000) where
  r0 := (146950814833/250000000000000000)
  k0 := (1812277768863689/500000000000000000)
  k6 := (2867596057741643/250000000000000000)
  q := (84412676773100851597/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14251]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14251]

theorem width_14252 : mW 14252 = 345593326763988 := by
  have hu : mW 14252 ≤ 345593326763988 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14252 ≤ 345593326763987 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14252 : RowArithmetic 14252 (279031057555332482553/250000000000000000000000) (37906564583294513352353/62500000000000000000000) (3491474710798057/500000000000000000000000) where
  r0 := (587741395073/1000000000000000000)
  k0 := (906091199186151/250000000000000000)
  k6 := (5734990905382167/500000000000000000)
  q := (84415638361621124449/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14252]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14252]

theorem width_14253 : mW 14253 = 345678204867813 := by
  have hu : mW 14253 ≤ 345678204867813 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14253 ≤ 345678204867812 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14253 : RowArithmetic 14253 (1116094615453281856139/1000000000000000000000000) (606494059024552756213891/1000000000000000000000000) (872709312706177/125000000000000000000000) where
  r0 := (117535908333/200000000000000000)
  k0 := (906043519795433/250000000000000000)
  k6 := (1433697429114243/125000000000000000)
  q := (84418599846242415631/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14253]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14253]

theorem width_14254 : mW 14254 = 345763097860705 := by
  have hu : mW 14254 ≤ 345763097860705 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14254 ≤ 345763097860704 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14254 : RowArithmetic 14254 (223213001528236010599/200000000000000000000000) (303241543124559745460977/500000000000000000000000) (6980399907048931/1000000000000000000000000) where
  r0 := (117523539821/200000000000000000)
  k0 := (3623983385033209/1000000000000000000)
  k6 := (5734588548703987/500000000000000000)
  q := (168843122453951318769/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14254]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14254]

theorem width_14255 : mW 14255 = 345848005744232 := by
  have hu : mW 14255 ≤ 345848005744232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14255 ≤ 345848005744231 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14255 : RowArithmetic 14255 (27900885169572132593/25000000000000000000000) (75809014375758799131129/125000000000000000000000) (3489562818844027/500000000000000000000000) where
  r0 := (58755586739/100000000000000000)
  k0 := (90594817857337/25000000000000000)
  k6 := (5734387402119499/500000000000000000)
  q := (84424522503831788033/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14255]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14255]

theorem width_14256 : mW 14256 = 345932928519959 := by
  have hu : mW 14256 ≤ 345932928519959 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14256 ≤ 345932928519958 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14256 : RowArithmetic 14256 (55800290643813040677/50000000000000000000000) (60646114529506348460229/100000000000000000000000) (6977851693460281/1000000000000000000000000) where
  r0 := (293747023259/500000000000000000)
  k0 := (452950258370009/125000000000000000)
  k6 := (1146837255339959/100000000000000000)
  q := (33770993470728692793/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14256]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14256]

theorem width_14257 : mW 14257 = 346017866189454 := by
  have hu : mW 14257 ≤ 346017866189454 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14257 ≤ 346017866189453 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14257 : RowArithmetic 14257 (1115976225919169047219/1000000000000000000000000) (606450177115756959409303/1000000000000000000000000) (1395315614851819/200000000000000000000000) where
  r0 := (587432236487/1000000000000000000)
  k0 := (3623411443030511/1000000000000000000)
  k6 := (11467970344882329/1000000000000000000)
  q := (42215222372978209861/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14257]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14257]

theorem width_14258 : mW 14258 = 346102818754284 := by
  have hu : mW 14258 ≤ 346102818754284 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14258 ≤ 346102818754283 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14258 : RowArithmetic 14258 (557973322954736918531/500000000000000000000000) (75804901308476135426513/125000000000000000000000) (3487652389989021/500000000000000000000000) where
  r0 := (587370437293/1000000000000000000)
  k0 := (905805210624039/250000000000000000)
  k6 := (11467568178679793/1000000000000000000)
  q := (168866811422493555651/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14258]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14258]

theorem width_14259 : mW 14259 = 346187786216016 := by
  have hu : mW 14259 ≤ 346187786216016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14259 ≤ 346187786216015 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14259 : RowArithmetic 14259 (557958536422519927663/500000000000000000000000) (606428245350878245318683/1000000000000000000000000) (6974031810510709/1000000000000000000000000) where
  r0 := (117461729787/200000000000000000)
  k0 := (3623030265357613/1000000000000000000)
  k6 := (2866791513696141/250000000000000000)
  q := (168872733145407461899/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14259]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14259]

theorem width_14260 : mW 14260 = 346272768576218 := by
  have hu : mW 14260 ≤ 346272768576218 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14260 ≤ 346272768576217 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14260 : RowArithmetic 14260 (44635500268949283517/40000000000000000000000) (303208640882311433761849/500000000000000000000000) (697275916575071/100000000000000000000000) where
  r0 := (36702929463/62500000000000000)
  k0 := (3622839711603151/1000000000000000000)
  k6 := (11466763973189223/1000000000000000000)
  q := (168878654660676403673/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14260]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14260]

theorem width_14261 : mW 14261 = 346357765836457 := by
  have hu : mW 14261 ≤ 346357765836457 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14261 ≤ 346357765836456 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14261 : RowArithmetic 14261 (69741121721463555399/62500000000000000000000) (606406319708701601596143/1000000000000000000000000) (6971486845591721/1000000000000000000000000) where
  r0 := (587185104711/1000000000000000000)
  k0 := (3622649181233377/1000000000000000000)
  k6 := (11466361933886357/1000000000000000000)
  q := (84442287984161111313/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14261]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14261]

theorem width_14262 : mW 14262 = 346442777998300 := by
  have hu : mW 14262 ≤ 346442777998300 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14262 ≤ 346442777998299 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14262 : RowArithmetic 14262 (11158283953019614409/10000000000000000000000) (303197679591386557551701/500000000000000000000000) (3485107424963731/500000000000000000000000) where
  r0 := (587123348841/1000000000000000000)
  k0 := (905614668560681/250000000000000000)
  k6 := (229319198737371/20000000000000000)
  q := (21111312133545844573/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14262]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14262]

theorem width_14263 : mW 14263 = 346527805063314 := by
  have hu : mW 14263 ≤ 346527805063314 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14263 ≤ 346527805063313 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14263 : RowArithmetic 14263 (13947485624965422249/12500000000000000000000) (121276880037299235287287/200000000000000000000000) (6968943178651697/1000000000000000000000000) where
  r0 := (117412320759/200000000000000000)
  k0 := (3622268190625627/1000000000000000000)
  k6 := (1433194747766049/125000000000000000)
  q := (21112052245103979943/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14263]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14263]

theorem width_14264 : mW 14264 = 346612847033068 := by
  have hu : mW 14264 ≤ 346612847033068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14264 ≤ 346612847033067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14264 : RowArithmetic 14264 (139471163953387714961/125000000000000000000000) (606373442719529682844053/1000000000000000000000000) (6967671831658191/1000000000000000000000000) where
  r0 := (586999869571/1000000000000000000)
  k0 := (3622077730379603/1000000000000000000)
  k6 := (11465156069658471/1000000000000000000)
  q := (42225584661434825419/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14264]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14264]

theorem width_14265 : mW 14265 = 346697903909128 := by
  have hu : mW 14265 ≤ 346697903909128 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14265 ≤ 346697903909127 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14265 : RowArithmetic 14265 (22314795603788709799/20000000000000000000000) (18948827711922896636153/31250000000000000000000) (435400050552551/62500000000000000000000) where
  r0 := (293469073083/500000000000000000)
  k0 := (1810943646749541/500000000000000000)
  k6 := (11464754199451381/1000000000000000000)
  q := (6756330364924438773/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14265]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14265]

theorem width_14266 : mW 14266 = 346782975693062 := by
  have hu : mW 14266 ≤ 346782975693062 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14266 ≤ 346782975693061 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14266 : RowArithmetic 14266 (5578551278410525537/5000000000000000000000) (60635153237216424391287/100000000000000000000000) (3482565055046723/500000000000000000000000) where
  r0 := (293438216789/500000000000000000)
  k0 := (3621696879981579/1000000000000000000)
  k6 := (2292870474299943/200000000000000000)
  q := (16891417939296866501/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14266]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14266]

theorem width_14267 : mW 14267 = 346868062386438 := by
  have hu : mW 14267 ≤ 346868062386438 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14267 ≤ 346868062386437 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14267 : RowArithmetic 14267 (223136147620596285227/200000000000000000000000) (75792572436385447813481/125000000000000000000000) (3481929867654999/500000000000000000000000) where
  r0 := (586814731803/1000000000000000000)
  k0 := (3621506489818437/1000000000000000000)
  k6 := (11463950585796067/1000000000000000000)
  q := (84460049727667103713/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14267]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14267]

theorem width_14268 : mW 14268 = 346953163990823 := by
  have hu : mW 14268 ≤ 346953163990823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14268 ≤ 346953163990822 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14268 : RowArithmetic 14268 (139456403431242082673/125000000000000000000000) (303164814068974996885987/500000000000000000000000) (6962589684384453/1000000000000000000000000) where
  r0 := (586753040839/1000000000000000000)
  k0 := (1810658061503583/500000000000000000)
  k6 := (2865887210583259/250000000000000000)
  q := (42231504827557352861/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14268]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14268]

theorem width_14269 : mW 14269 = 347038280507786 := by
  have hu : mW 14269 ≤ 347038280507786 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14269 ≤ 347038280507785 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14269 : RowArithmetic 14269 (1115621723720842816193/1000000000000000000000000) (606318678312422927765697/1000000000000000000000000) (1740329989302699/250000000000000000000000) where
  r0 := (586691360683/1000000000000000000)
  k0 := (3621125779542193/1000000000000000000)
  k6 := (11463147141103221/1000000000000000000)
  q := (33786387791535217623/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14269]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14269]

theorem width_14270 : mW 14270 = 347123411938893 := by
  have hu : mW 14270 ≤ 347123411938893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14270 ≤ 347123411938892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14270 : RowArithmetic 14270 (139449028364196787721/125000000000000000000000) (303153865007080940348721/500000000000000000000000) (3480025276841557/500000000000000000000000) where
  r0 := (586629691333/1000000000000000000)
  k0 := (1810467729710513/500000000000000000)
  k6 := (5731372741049611/500000000000000000)
  q := (84468929198848022333/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14270]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14270]

theorem width_14271 : mW 14271 = 347208558285714 := by
  have hu : mW 14271 ≤ 347208558285714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14271 ≤ 347208558285713 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14271 : RowArithmetic 14271 (1115562737026004269261/1000000000000000000000000) (151574195810706630949357/250000000000000000000000) (6958781473695459/1000000000000000000000000) where
  r0 := (293284016393/500000000000000000)
  k0 := (3620745162638087/1000000000000000000)
  k6 := (11462343865313643/1000000000000000000)
  q := (84471888815155542253/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14271]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14271]

theorem width_14272 : mW 14272 = 347293719549815 := by
  have hu : mW 14272 ≤ 347293719549815 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14272 ≤ 347293719549814 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14272 : RowArithmetic 14272 (223106650811201760001/200000000000000000000000) (121257167599615311397129/200000000000000000000000) (3478756358571003/500000000000000000000000) where
  r0 := (7331329813/12500000000000000)
  k0 := (3620554889190883/1000000000000000000)
  k6 := (11461942290739087/1000000000000000000)
  q := (168949696655543007223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14272]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14272]

theorem width_14273 : mW 14273 = 347378895732764 := by
  have hu : mW 14273 ≤ 347378895732764 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14273 ≤ 347378895732763 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14273 : RowArithmetic 14273 (1115503778001463762313/1000000000000000000000000) (303137447139785891850807/500000000000000000000000) (6956244283916933/1000000000000000000000000) where
  r0 := (586444748091/1000000000000000000)
  k0 := (1810182319535373/500000000000000000)
  k6 := (5730770379184081/500000000000000000)
  q := (84477807736706804293/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14273]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14273]

theorem width_14274 : mW 14274 = 347464086836131 := by
  have hu : mW 14274 ≤ 347464086836131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14274 ≤ 347464086836130 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14274 : RowArithmetic 14274 (557737154430122406593/500000000000000000000000) (1894574850271788074507/3125000000000000000000) (347748808695721/50000000000000000000000) where
  r0 := (293191560969/500000000000000000)
  k0 := (905043603069567/250000000000000000)
  k6 := (5730569634096737/500000000000000000)
  q := (42240383520986170137/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14274]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14274]

theorem width_14275 : mW 14275 = 347549292861482 := by
  have hu : mW 14275 ≤ 347549292861482 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14275 ≤ 347549292861481 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14275 : RowArithmetic 14275 (1115444846630230535973/1000000000000000000000000) (606253011419937804567017/1000000000000000000000000) (6953708387028773/1000000000000000000000000) where
  r0 := (586321506577/1000000000000000000)
  k0 := (1809992104402389/500000000000000000)
  k6 := (2865184455051909/250000000000000000)
  q := (33793490497431602249/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14275]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14275]

theorem width_14276 : mW 14276 = 347634513810386 := by
  have hu : mW 14276 ≤ 347634513810386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14276 ≤ 347634513810385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14276 : RowArithmetic 14276 (557707695654649389283/500000000000000000000000) (151560518069532185429023/250000000000000000000000) (173811023078857/25000000000000000000000) where
  r0 := (117251980401/200000000000000000)
  k0 := (361979402864469/100000000000000000)
  k6 := (11460336414403257/1000000000000000000)
  q := (42243342670768846249/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14276]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14276]

theorem width_14277 : mW 14277 = 347719749684411 := by
  have hu : mW 14277 ≤ 347719749684411 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14277 ≤ 347719749684410 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14277 : RowArithmetic 14277 (1115385942895328745107/1000000000000000000000000) (606231134661205298392099/1000000000000000000000000) (6951173782185293/1000000000000000000000000) where
  r0 := (586198308221/1000000000000000000)
  k0 := (3619603871798591/1000000000000000000)
  k6 := (1432491881346619/125000000000000000)
  q := (84489644335859291153/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14277]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14277]

theorem width_14278 : mW 14278 = 347805000485125 := by
  have hu : mW 14278 ≤ 347805000485125 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14278 ≤ 347805000485124 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14278 : RowArithmetic 14278 (1115356501386200472477/1000000000000000000000000) (606220198568827836166461/1000000000000000000000000) (1389981392803241/200000000000000000000000) where
  r0 := (293068362611/500000000000000000)
  k0 := (723882747652179/200000000000000000)
  k6 := (1432441716163667/125000000000000000)
  q := (168985206453109379867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14278]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14278]

theorem width_14279 : mW 14279 = 347890266214097 := by
  have hu : mW 14279 ≤ 347890266214097 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14279 ≤ 347890266214096 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14279 : RowArithmetic 14279 (278831766694948577017/250000000000000000000000) (606209264000656756675353/1000000000000000000000000) (1389728093708287/200000000000000000000000) where
  r0 := (146518788251/250000000000000000)
  k0 := (1809611814011461/500000000000000000)
  k6 := (5729566225002513/500000000000000000)
  q := (84495562013634775279/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14279]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14279]

theorem width_14280 : mW 14280 = 347975546872895 := by
  have hu : mW 14280 ≤ 347975546872895 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14280 ≤ 347975546872894 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14280 : RowArithmetic 14280 (278824409768497988403/250000000000000000000000) (303099165478176324530371/500000000000000000000000) (868421786956933/125000000000000000000000) where
  r0 := (293006795783/500000000000000000)
  k0 := (1809516770542629/500000000000000000)
  k6 := (5729365606426321/500000000000000000)
  q := (168997041394220863443/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14280]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14280]

theorem width_14281 : mW 14281 = 348060842463087 := by
  have hu : mW 14281 ≤ 348060842463087 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14281 ≤ 348060842463086 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14281 : RowArithmetic 14281 (223053643653335188463/200000000000000000000000) (606187399435576183447673/1000000000000000000000000) (6946108445252817/1000000000000000000000000) where
  r0 := (73244005113/125000000000000000)
  k0 := (1809421738719611/500000000000000000)
  k6 := (2864582504461201/250000000000000000)
  q := (8450147927699254189/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14281]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14281]

theorem width_14282 : mW 14282 = 348146152986242 := by
  have hu : mW 14282 ≤ 348146152986242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14282 ≤ 348146152986241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14282 : RowArithmetic 14282 (278809701088932279317/250000000000000000000000) (151544117359497032535151/250000000000000000000000) (173621072930701/25000000000000000000000) where
  r0 := (585890501017/1000000000000000000)
  k0 := (904663359271349/250000000000000000)
  k6 := (2291585772994827/200000000000000000)
  q := (42252218876645993253/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14282]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14282]

theorem width_14283 : mW 14283 = 348231478443928 := by
  have hu : mW 14283 ≤ 348231478443928 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14283 ≤ 348231478443927 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14283 : RowArithmetic 14283 (223041879467807134799/200000000000000000000000) (606165540963249351429923/1000000000000000000000000) (1388715542295149/200000000000000000000000) where
  r0 := (5858289719/10000000000000000)
  k0 := (3618463420012009/1000000000000000000)
  k6 := (11457527754233259/1000000000000000000)
  q := (21126849031504911097/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14283]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14283]

theorem width_14284 : mW 14284 = 348316818837714 := by
  have hu : mW 14284 ≤ 348316818837714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14284 ≤ 348316818837713 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14284 : RowArithmetic 14284 (1115179997214480117489/1000000000000000000000000) (24246184560440834254531/40000000000000000000000) (1388462565578113/200000000000000000000000) where
  r0 := (585767453553/1000000000000000000)
  k0 := (3618273426222727/1000000000000000000)
  k6 := (11457126685614803/1000000000000000000)
  q := (1690207087903727849/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14284]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14284]

theorem width_14285 : mW 14285 = 348402174169168 := by
  have hu : mW 14285 ≤ 348402174169168 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14285 ≤ 348402174169167 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14285 : RowArithmetic 14285 (1115150603979948303909/1000000000000000000000000) (606143688580963667446013/1000000000000000000000000) (3470524133183599/500000000000000000000000) where
  r0 := (585705945971/1000000000000000000)
  k0 := (3618083455705777/1000000000000000000)
  k6 := (2291345131822279/200000000000000000)
  q := (42256656280401552851/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14285]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14285]

theorem width_14286 : mW 14286 = 348487544439860 := by
  have hu : mW 14286 ≤ 348487544439860 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14286 ≤ 348487544439859 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14286 : RowArithmetic 14286 (1115121217633325878149/1000000000000000000000000) (303066382336369506349721/500000000000000000000000) (867473003350043/125000000000000000000000) where
  r0 := (585644449153/1000000000000000000)
  k0 := (1808946754230867/500000000000000000)
  k6 := (716020292169729/62500000000000000)
  q := (169032541245761314503/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14286]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14286]

theorem width_14287 : mW 14287 = 348572929651357 := by
  have hu : mW 14287 ≤ 348572929651357 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14287 ≤ 348572929651356 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14287 : RowArithmetic 14287 (1115091838172500876061/1000000000000000000000000) (151530460571502032763019/250000000000000000000000) (1387704021816961/200000000000000000000000) where
  r0 := (73197870387/125000000000000000)
  k0 := (1808851792242499/500000000000000000)
  k6 := (5727961866210121/500000000000000000)
  q := (42259614290714959151/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14287]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14287]

theorem width_14288 : mW 14288 = 348658329805229 := by
  have hu : mW 14288 ≤ 348658329805229 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14288 ≤ 348658329805228 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14288 : RowArithmetic 14288 (139382808199420075187/125000000000000000000000) (606110921420432474227157/1000000000000000000000000) (867157064139421/125000000000000000000000) where
  r0 := (146380371949/250000000000000000)
  k0 := (3617513683766877/1000000000000000000)
  k6 := (2863880708054441/250000000000000000)
  q := (169044372872923516313/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14288]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14288]

theorem width_14289 : mW 14289 = 348743744903045 := by
  have hu : mW 14289 ≤ 348743744903045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14289 ≤ 348743744903044 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14289 : RowArithmetic 14289 (1115033099899793707789/1000000000000000000000000) (606100002075673515975723/1000000000000000000000000) (1733998309696721/250000000000000000000000) where
  r0 := (585460023253/1000000000000000000)
  k0 := (723464761262207/200000000000000000)
  k6 := (11455121974100863/1000000000000000000)
  q := (169050288375974088429/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14289]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14289]

theorem width_14290 : mW 14290 = 348829174946372 := by
  have hu : mW 14290 ≤ 348829174946372 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14290 ≤ 348829174946371 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14290 : RowArithmetic 14290 (278750935270922678937/250000000000000000000000) (303044542125696412040409/500000000000000000000000) (6934730285994283/1000000000000000000000000) where
  r0 := (292699284731/500000000000000000)
  k0 := (3617133952105687/1000000000000000000)
  k6 := (5727360579031089/500000000000000000)
  q := (3381124073440665679/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14290]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14290]

theorem width_14291 : mW 14291 = 348914619936781 := by
  have hu : mW 14291 ≤ 348914619936781 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14291 ≤ 348914619936780 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14291 : RowArithmetic 14291 (278743597286235223893/250000000000000000000000) (606078167947252089847717/1000000000000000000000000) (6933467654632461/1000000000000000000000000) where
  r0 := (585337126421/1000000000000000000)
  k0 := (723388824229663/200000000000000000)
  k6 := (11454320384094347/1000000000000000000)
  q := (84531059380561415037/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14291]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14291]

theorem width_14292 : mW 14292 = 349000079875841 := by
  have hu : mW 14292 ≤ 349000079875841 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14292 ≤ 349000079875840 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14292 : RowArithmetic 14292 (1114945044081435384939/1000000000000000000000000) (606067253162913166393817/1000000000000000000000000) (3466102672298199/500000000000000000000000) where
  r0 := (36579730883/62500000000000000)
  k0 := (9041885783591/2500000000000000)
  k6 := (1145391965219001/100000000000000000)
  q := (84534016821632225097/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14292]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14292]

theorem width_14293 : mW 14293 = 349085554765119 := by
  have hu : mW 14293 ≤ 349085554765119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14293 ≤ 349085554765118 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14293 : RowArithmetic 14293 (1114915705891067186471/1000000000000000000000000) (606056339898037940404451/1000000000000000000000000) (6930943355781153/1000000000000000000000000) where
  r0 := (29260713629/50000000000000000)
  k0 := (904141132241083/250000000000000000)
  k6 := (11453518962341811/1000000000000000000)
  q := (42268487079619965977/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14293]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14293]

theorem width_14294 : mW 14294 = 349171044606186 := by
  have hu : mW 14294 ≤ 349171044606186 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14294 ≤ 349171044606185 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14294 : RowArithmetic 14294 (139360796821466006683/125000000000000000000000) (606045428152288417385799/1000000000000000000000000) (866210211010219/125000000000000000000000) where
  r0 := (23406114471/40000000000000000)
  k0 := (3616374767729591/1000000000000000000)
  k6 := (5726559157271197/500000000000000000)
  q := (16907986278679078701/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14294]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14294]

theorem width_14295 : mW 14295 = 349256549400611 := by
  have hu : mW 14295 ≤ 349256549400611 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14295 ≤ 349256549400610 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14295 : RowArithmetic 14295 (222971410024262320833/200000000000000000000000) (75754314740665838437561/125000000000000000000000) (6928420341393303/1000000000000000000000000) where
  r0 := (585091461709/1000000000000000000)
  k0 := (3616185029723473/1000000000000000000)
  k6 := (2863179427196101/250000000000000000)
  q := (169085777048218931501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14295]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14295]

theorem width_14296 : mW 14296 = 349342069149963 := by
  have hu : mW 14296 ≤ 349342069149963 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14296 ≤ 349342069149962 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14296 : RowArithmetic 14296 (557413866268856141419/500000000000000000000000) (606023609216815011314421/1000000000000000000000000) (3463579657805477/500000000000000000000000) where
  r0 := (29251503619/50000000000000000)
  k0 := (3615995314943453/1000000000000000000)
  k6 := (1145231714506049/100000000000000000)
  q := (169091691102786005581/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14296]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14296]

theorem width_14297 : mW 14297 = 349427603855810 := by
  have hu : mW 14297 ≤ 349427603855810 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14297 ≤ 349427603855809 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14297 : RowArithmetic 14297 (55739921090941293867/50000000000000000000000) (12120254040528314077499/20000000000000000000000) (6925898610629919/1000000000000000000000000) where
  r0 := (292484346893/500000000000000000)
  k0 := (3615805623387007/1000000000000000000)
  k6 := (5725958311681651/500000000000000000)
  q := (21137200618814214207/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14297]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14297]

theorem width_14298 : mW 14298 = 349513153519723 := by
  have hu : mW 14298 ≤ 349513153519723 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14298 ≤ 349513153519722 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14298 : RowArithmetic 14298 (557384558981273723263/500000000000000000000000) (151500449088447778947181/250000000000000000000000) (1384927645269079/200000000000000000000000) where
  r0 := (584907325923/1000000000000000000)
  k0 := (3615615955045427/1000000000000000000)
  k6 := (1145151614368549/100000000000000000)
  q := (10568969911963984771/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14298]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14298]

theorem width_14299 : mW 14299 = 349598718143271 := by
  have hu : mW 14299 ≤ 349598718143271 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14299 ≤ 349598718143270 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14299 : RowArithmetic 14299 (1114739820966773910841/1000000000000000000000000) (605990892198603839177097/1000000000000000000000000) (346168908132633/50000000000000000000000) where
  r0 := (58484596879/100000000000000000)
  k0 := (144617052396771/40000000000000000)
  k6 := (2862778926504927/250000000000000000)
  q := (169109432025537830437/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14299]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14299]

theorem width_14300 : mW 14300 = 349684297728024 := by
  have hu : mW 14300 ≤ 349684297728024 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14300 ≤ 349684297728023 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14300 : RowArithmetic 14300 (27867763270735062443/25000000000000000000000) (121195997912103303050031/200000000000000000000000) (865264802430877/125000000000000000000000) where
  r0 := (584784622383/1000000000000000000)
  k0 := (22595229299999/6250000000000000)
  k6 := (2862678827589653/250000000000000000)
  q := (84557672626438814491/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14300]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14300]

theorem width_14301 : mW 14301 = 349769892275550 := by
  have hu : mW 14301 ≤ 349769892275550 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14301 ≤ 349769892275549 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14301 : RowArithmetic 14301 (557340623774166146829/500000000000000000000000) (605969088439191821966517/1000000000000000000000000) (6920858996623847/1000000000000000000000000) where
  r0 := (5847232867/10000000000000000)
  k0 := (225940443080287/62500000000000000)
  k6 := (5725157478347429/500000000000000000)
  q := (169121258273464841201/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14301]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14301]

theorem width_14302 : mW 14302 = 349855501787419 := by
  have hu : mW 14302 ≤ 349855501787419 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14302 ≤ 349855501787418 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14302 : RowArithmetic 14302 (22293039422429243479/20000000000000000000000) (302979094417146307216927/500000000000000000000000) (6919599894078541/1000000000000000000000000) where
  r0 := (584661961739/1000000000000000000)
  k0 := (3614857513771/1000000000000000)
  k6 := (2289982929004221/200000000000000000)
  q := (42281792771830288133/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14302]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14302]

theorem width_14303 : mW 14303 = 349941126265201 := by
  have hu : mW 14303 ≤ 349941126265201 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14303 ≤ 349941126265200 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14303 : RowArithmetic 14303 (1114622701546691837829/1000000000000000000000000) (151486822686370454356377/250000000000000000000000) (6918341111706527/1000000000000000000000000) where
  r0 := (73075080937/125000000000000000)
  k0 := (1807333980725173/500000000000000000)
  k6 := (5724757187665007/500000000000000000)
  q := (1353064669555745957/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14303]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14303]

theorem width_14304 : mW 14304 = 350026765710466 := by
  have hu : mW 14304 ≤ 350026765710466 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14304 ≤ 350026765710465 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14304 : RowArithmetic 14304 (222918687764384361609/200000000000000000000000) (151484098543105626965589/250000000000000000000000) (6917082649403279/1000000000000000000000000) where
  r0 := (58453934397/100000000000000000)
  k0 := (361447843232319/100000000000000000)
  k6 := (5724557073807123/500000000000000000)
  q := (21142374511865974417/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14304]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14304]

theorem width_14305 : mW 14305 = 350112420124783 := by
  have hu : mW 14305 ≤ 350112420124783 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14305 ≤ 350112420124782 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14305 : RowArithmetic 14305 (278641045736263486689/250000000000000000000000) (75740687389347222526459/125000000000000000000000) (6915824507064333/1000000000000000000000000) where
  r0 := (146119512789/250000000000000000)
  k0 := (3614288926377719/1000000000000000000)
  k6 := (5724356980933233/500000000000000000)
  q := (10571556768045092421/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14305]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14305]

theorem width_14306 : mW 14306 = 350198089509722 := by
  have hu : mW 14306 ≤ 350198089509722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14306 ≤ 350198089509721 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14306 : RowArithmetic 14306 (69658433369624401367/62500000000000000000000) (605914605572210906136361/1000000000000000000000000) (3457283342292623/500000000000000000000000) where
  r0 := (292208384527/500000000000000000)
  k0 := (180704972180879/50000000000000000)
  k6 := (572415690903967/50000000000000000)
  q := (169150820275870965107/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14306]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14306]

theorem width_14307 : mW 14307 = 350283773866853 := by
  have hu : mW 14307 ≤ 350283773866853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14307 ≤ 350283773866852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14307 : RowArithmetic 14307 (1114505691726634223569/1000000000000000000000000) (121180742708877044764023/200000000000000000000000) (6913309181861619/1000000000000000000000000) where
  r0 := (29217774883/50000000000000000)
  k0 := (903477496008513/250000000000000000)
  k6 := (2289582743249107/200000000000000000)
  q := (10572295753524870059/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14307]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14307]

theorem width_14308 : mW 14308 = 350369473197746 := by
  have hu : mW 14308 ≤ 350369473197746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14308 ≤ 350369473197745 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14308 : RowArithmetic 14308 (557238228190444581939/500000000000000000000000) (302946411515482091085281/500000000000000000000000) (6912051998789097/1000000000000000000000000) where
  r0 := (584294236971/1000000000000000000)
  k0 := (3613720547621503/1000000000000000000)
  k6 := (11447513656357721/1000000000000000000)
  q := (42290660907581002239/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14308]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14308]

theorem width_14309 : mW 14309 = 350455187503970 := by
  have hu : mW 14309 ≤ 350455187503970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14309 ≤ 350455187503969 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14309 : RowArithmetic 14309 (278611806968665097933/250000000000000000000000) (151470483507902833688323/250000000000000000000000) (3455397567631693/500000000000000000000000) where
  r0 := (292116493493/500000000000000000)
  k0 := (3613531134380483/1000000000000000000)
  k6 := (11447113638408569/1000000000000000000)
  q := (42292138749417722017/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14309]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14309]

theorem width_14310 : mW 14310 = 350540916787096 := by
  have hu : mW 14310 ≤ 350540916787096 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14310 ≤ 350540916787095 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14310 : RowArithmetic 14310 (139302250775731605717/125000000000000000000000) (24234841861839614015643/40000000000000000000000) (3454769295590097/500000000000000000000000) where
  r0 := (584171747701/1000000000000000000)
  k0 := (903335436075567/250000000000000000)
  k6 := (357709801949711/31250000000000000)
  q := (8458723307923010671/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14310]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14310]

theorem width_14311 : mW 14311 = 350626661048694 := by
  have hu : mW 14311 ≤ 350626661048694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14311 ≤ 350626661048693 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14311 : RowArithmetic 14311 (222877758274474560197/200000000000000000000000) (60586016057376495660901/100000000000000000000000) (3454141183217647/500000000000000000000000) where
  r0 := (584110519113/1000000000000000000)
  k0 := (3613152377381219/1000000000000000000)
  k6 := (5723156864148473/500000000000000000)
  q := (10573773569544602273/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14311]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14311]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14237 then ⟨(558284643956201136453/500000000000000000000000), (9479216126799341194693/15625000000000000000000), (7002112334951073/1000000000000000000000000)⟩ else
  if n = 14238 then ⟨(1116539568547964702429/1000000000000000000000000), (303329417387494444108031/500000000000000000000000), (7000832521991881/1000000000000000000000000)⟩ else
  if n = 14239 then ⟨(1116509856171651264299/1000000000000000000000000), (75830979871586177845179/125000000000000000000000), (6999553035982809/1000000000000000000000000)⟩ else
  if n = 14240 then ⟨(55824007539065556659/50000000000000000000000), (606636844707915756174083/1000000000000000000000000), (6998273876816631/1000000000000000000000000)⟩ else
  if n = 14241 then ⟨(1116450452374794330539/1000000000000000000000000), (606625851980324401928559/1000000000000000000000000), (6996995044386169/1000000000000000000000000)⟩ else
  if n = 14242 then ⟨(1116420760949951194469/1000000000000000000000000), (606614860789571967873727/1000000000000000000000000), (3497858269292133/500000000000000000000000)⟩ else
  if n = 14243 then ⟨(1116391076504633439409/1000000000000000000000000), (606603871135315077301957/1000000000000000000000000), (699443835930383/100000000000000000000000)⟩ else
  if n = 14244 then ⟨(558180699518346812657/500000000000000000000000), (606592883017210619136277/1000000000000000000000000), (3496580253218907/500000000000000000000000)⟩ else
  if n = 14245 then ⟨(558165864271992578611/500000000000000000000000), (303290948217457743740459/500000000000000000000000), (6991882979879213/1000000000000000000000000)⟩ else
  if n = 14246 then ⟨(1116302065024361227057/1000000000000000000000000), (303285455694043309493469/500000000000000000000000), (6990605779521027/1000000000000000000000000)⟩ else
  if n = 14247 then ⟨(223254481695135491741/200000000000000000000000), (606559927876381237642707/1000000000000000000000000), (6989328905256361/1000000000000000000000000)⟩ else
  if n = 14248 then ⟨(1116242758895788733627/1000000000000000000000000), (151637236474864124391343/250000000000000000000000), (69880523569783/10000000000000000000000)⟩ else
  if n = 14249 then ⟨(1116213116282551834851/1000000000000000000000000), (151634491364242433775227/250000000000000000000000), (3493388067290009/500000000000000000000000)⟩ else
  if n = 14250 then ⟨(1116183480633824388349/1000000000000000000000000), (30326349327428920676321/50000000000000000000000), (698550023795473/100000000000000000000000)⟩ else
  if n = 14251 then ⟨(1116153851947464334793/1000000000000000000000000), (4852128073391520044341/8000000000000000000000), (3492112333497837/500000000000000000000000)⟩ else
  if n = 14252 then ⟨(279031057555332482553/250000000000000000000000), (37906564583294513352353/62500000000000000000000), (3491474710798057/500000000000000000000000)⟩ else
  if n = 14253 then ⟨(1116094615453281856139/1000000000000000000000000), (606494059024552756213891/1000000000000000000000000), (872709312706177/125000000000000000000000)⟩ else
  if n = 14254 then ⟨(223213001528236010599/200000000000000000000000), (303241543124559745460977/500000000000000000000000), (6980399907048931/1000000000000000000000000)⟩ else
  if n = 14255 then ⟨(27900885169572132593/25000000000000000000000), (75809014375758799131129/125000000000000000000000), (3489562818844027/500000000000000000000000)⟩ else
  if n = 14256 then ⟨(55800290643813040677/50000000000000000000000), (60646114529506348460229/100000000000000000000000), (6977851693460281/1000000000000000000000000)⟩ else
  if n = 14257 then ⟨(1115976225919169047219/1000000000000000000000000), (606450177115756959409303/1000000000000000000000000), (1395315614851819/200000000000000000000000)⟩ else
  if n = 14258 then ⟨(557973322954736918531/500000000000000000000000), (75804901308476135426513/125000000000000000000000), (3487652389989021/500000000000000000000000)⟩ else
  if n = 14259 then ⟨(557958536422519927663/500000000000000000000000), (606428245350878245318683/1000000000000000000000000), (6974031810510709/1000000000000000000000000)⟩ else
  if n = 14260 then ⟨(44635500268949283517/40000000000000000000000), (303208640882311433761849/500000000000000000000000), (697275916575071/100000000000000000000000)⟩ else
  if n = 14261 then ⟨(69741121721463555399/62500000000000000000000), (606406319708701601596143/1000000000000000000000000), (6971486845591721/1000000000000000000000000)⟩ else
  if n = 14262 then ⟨(11158283953019614409/10000000000000000000000), (303197679591386557551701/500000000000000000000000), (3485107424963731/500000000000000000000000)⟩ else
  if n = 14263 then ⟨(13947485624965422249/12500000000000000000000), (121276880037299235287287/200000000000000000000000), (6968943178651697/1000000000000000000000000)⟩ else
  if n = 14264 then ⟨(139471163953387714961/125000000000000000000000), (606373442719529682844053/1000000000000000000000000), (6967671831658191/1000000000000000000000000)⟩ else
  if n = 14265 then ⟨(22314795603788709799/20000000000000000000000), (18948827711922896636153/31250000000000000000000), (435400050552551/62500000000000000000000)⟩ else
  if n = 14266 then ⟨(5578551278410525537/5000000000000000000000), (60635153237216424391287/100000000000000000000000), (3482565055046723/500000000000000000000000)⟩ else
  if n = 14267 then ⟨(223136147620596285227/200000000000000000000000), (75792572436385447813481/125000000000000000000000), (3481929867654999/500000000000000000000000)⟩ else
  if n = 14268 then ⟨(139456403431242082673/125000000000000000000000), (303164814068974996885987/500000000000000000000000), (6962589684384453/1000000000000000000000000)⟩ else
  if n = 14269 then ⟨(1115621723720842816193/1000000000000000000000000), (606318678312422927765697/1000000000000000000000000), (1740329989302699/250000000000000000000000)⟩ else
  if n = 14270 then ⟨(139449028364196787721/125000000000000000000000), (303153865007080940348721/500000000000000000000000), (3480025276841557/500000000000000000000000)⟩ else
  if n = 14271 then ⟨(1115562737026004269261/1000000000000000000000000), (151574195810706630949357/250000000000000000000000), (6958781473695459/1000000000000000000000000)⟩ else
  if n = 14272 then ⟨(223106650811201760001/200000000000000000000000), (121257167599615311397129/200000000000000000000000), (3478756358571003/500000000000000000000000)⟩ else
  if n = 14273 then ⟨(1115503778001463762313/1000000000000000000000000), (303137447139785891850807/500000000000000000000000), (6956244283916933/1000000000000000000000000)⟩ else
  if n = 14274 then ⟨(557737154430122406593/500000000000000000000000), (1894574850271788074507/3125000000000000000000), (347748808695721/50000000000000000000000)⟩ else
  if n = 14275 then ⟨(1115444846630230535973/1000000000000000000000000), (606253011419937804567017/1000000000000000000000000), (6953708387028773/1000000000000000000000000)⟩ else
  if n = 14276 then ⟨(557707695654649389283/500000000000000000000000), (151560518069532185429023/250000000000000000000000), (173811023078857/25000000000000000000000)⟩ else
  if n = 14277 then ⟨(1115385942895328745107/1000000000000000000000000), (606231134661205298392099/1000000000000000000000000), (6951173782185293/1000000000000000000000000)⟩ else
  if n = 14278 then ⟨(1115356501386200472477/1000000000000000000000000), (606220198568827836166461/1000000000000000000000000), (1389981392803241/200000000000000000000000)⟩ else
  if n = 14279 then ⟨(278831766694948577017/250000000000000000000000), (606209264000656756675353/1000000000000000000000000), (1389728093708287/200000000000000000000000)⟩ else
  if n = 14280 then ⟨(278824409768497988403/250000000000000000000000), (303099165478176324530371/500000000000000000000000), (868421786956933/125000000000000000000000)⟩ else
  if n = 14281 then ⟨(223053643653335188463/200000000000000000000000), (606187399435576183447673/1000000000000000000000000), (6946108445252817/1000000000000000000000000)⟩ else
  if n = 14282 then ⟨(278809701088932279317/250000000000000000000000), (151544117359497032535151/250000000000000000000000), (173621072930701/25000000000000000000000)⟩ else
  if n = 14283 then ⟨(223041879467807134799/200000000000000000000000), (606165540963249351429923/1000000000000000000000000), (1388715542295149/200000000000000000000000)⟩ else
  if n = 14284 then ⟨(1115179997214480117489/1000000000000000000000000), (24246184560440834254531/40000000000000000000000), (1388462565578113/200000000000000000000000)⟩ else
  if n = 14285 then ⟨(1115150603979948303909/1000000000000000000000000), (606143688580963667446013/1000000000000000000000000), (3470524133183599/500000000000000000000000)⟩ else
  if n = 14286 then ⟨(1115121217633325878149/1000000000000000000000000), (303066382336369506349721/500000000000000000000000), (867473003350043/125000000000000000000000)⟩ else
  if n = 14287 then ⟨(1115091838172500876061/1000000000000000000000000), (151530460571502032763019/250000000000000000000000), (1387704021816961/200000000000000000000000)⟩ else
  if n = 14288 then ⟨(139382808199420075187/125000000000000000000000), (606110921420432474227157/1000000000000000000000000), (867157064139421/125000000000000000000000)⟩ else
  if n = 14289 then ⟨(1115033099899793707789/1000000000000000000000000), (606100002075673515975723/1000000000000000000000000), (1733998309696721/250000000000000000000000)⟩ else
  if n = 14290 then ⟨(278750935270922678937/250000000000000000000000), (303044542125696412040409/500000000000000000000000), (6934730285994283/1000000000000000000000000)⟩ else
  if n = 14291 then ⟨(278743597286235223893/250000000000000000000000), (606078167947252089847717/1000000000000000000000000), (6933467654632461/1000000000000000000000000)⟩ else
  if n = 14292 then ⟨(1114945044081435384939/1000000000000000000000000), (606067253162913166393817/1000000000000000000000000), (3466102672298199/500000000000000000000000)⟩ else
  if n = 14293 then ⟨(1114915705891067186471/1000000000000000000000000), (606056339898037940404451/1000000000000000000000000), (6930943355781153/1000000000000000000000000)⟩ else
  if n = 14294 then ⟨(139360796821466006683/125000000000000000000000), (606045428152288417385799/1000000000000000000000000), (866210211010219/125000000000000000000000)⟩ else
  if n = 14295 then ⟨(222971410024262320833/200000000000000000000000), (75754314740665838437561/125000000000000000000000), (6928420341393303/1000000000000000000000000)⟩ else
  if n = 14296 then ⟨(557413866268856141419/500000000000000000000000), (606023609216815011314421/1000000000000000000000000), (3463579657805477/500000000000000000000000)⟩ else
  if n = 14297 then ⟨(55739921090941293867/50000000000000000000000), (12120254040528314077499/20000000000000000000000), (6925898610629919/1000000000000000000000000)⟩ else
  if n = 14298 then ⟨(557384558981273723263/500000000000000000000000), (151500449088447778947181/250000000000000000000000), (1384927645269079/200000000000000000000000)⟩ else
  if n = 14299 then ⟨(1114739820966773910841/1000000000000000000000000), (605990892198603839177097/1000000000000000000000000), (346168908132633/50000000000000000000000)⟩ else
  if n = 14300 then ⟨(27867763270735062443/25000000000000000000000), (121195997912103303050031/200000000000000000000000), (865264802430877/125000000000000000000000)⟩ else
  if n = 14301 then ⟨(557340623774166146829/500000000000000000000000), (605969088439191821966517/1000000000000000000000000), (6920858996623847/1000000000000000000000000)⟩ else
  if n = 14302 then ⟨(22293039422429243479/20000000000000000000000), (302979094417146307216927/500000000000000000000000), (6919599894078541/1000000000000000000000000)⟩ else
  if n = 14303 then ⟨(1114622701546691837829/1000000000000000000000000), (151486822686370454356377/250000000000000000000000), (6918341111706527/1000000000000000000000000)⟩ else
  if n = 14304 then ⟨(222918687764384361609/200000000000000000000000), (151484098543105626965589/250000000000000000000000), (6917082649403279/1000000000000000000000000)⟩ else
  if n = 14305 then ⟨(278641045736263486689/250000000000000000000000), (75740687389347222526459/125000000000000000000000), (6915824507064333/1000000000000000000000000)⟩ else
  if n = 14306 then ⟨(69658433369624401367/62500000000000000000000), (605914605572210906136361/1000000000000000000000000), (3457283342292623/500000000000000000000000)⟩ else
  if n = 14307 then ⟨(1114505691726634223569/1000000000000000000000000), (121180742708877044764023/200000000000000000000000), (6913309181861619/1000000000000000000000000)⟩ else
  if n = 14308 then ⟨(557238228190444581939/500000000000000000000000), (302946411515482091085281/500000000000000000000000), (6912051998789097/1000000000000000000000000)⟩ else
  if n = 14309 then ⟨(278611806968665097933/250000000000000000000000), (151470483507902833688323/250000000000000000000000), (3455397567631693/500000000000000000000000)⟩ else
  if n = 14310 then ⟨(139302250775731605717/125000000000000000000000), (24234841861839614015643/40000000000000000000000), (3454769295590097/500000000000000000000000)⟩ else
  ⟨(222877758274474560197/200000000000000000000000), (60586016057376495660901/100000000000000000000000), (3454141183217647/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14237 ≤ n) (hb : n ≤ 14311) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14237
  · exact row_14238
  · exact row_14239
  · exact row_14240
  · exact row_14241
  · exact row_14242
  · exact row_14243
  · exact row_14244
  · exact row_14245
  · exact row_14246
  · exact row_14247
  · exact row_14248
  · exact row_14249
  · exact row_14250
  · exact row_14251
  · exact row_14252
  · exact row_14253
  · exact row_14254
  · exact row_14255
  · exact row_14256
  · exact row_14257
  · exact row_14258
  · exact row_14259
  · exact row_14260
  · exact row_14261
  · exact row_14262
  · exact row_14263
  · exact row_14264
  · exact row_14265
  · exact row_14266
  · exact row_14267
  · exact row_14268
  · exact row_14269
  · exact row_14270
  · exact row_14271
  · exact row_14272
  · exact row_14273
  · exact row_14274
  · exact row_14275
  · exact row_14276
  · exact row_14277
  · exact row_14278
  · exact row_14279
  · exact row_14280
  · exact row_14281
  · exact row_14282
  · exact row_14283
  · exact row_14284
  · exact row_14285
  · exact row_14286
  · exact row_14287
  · exact row_14288
  · exact row_14289
  · exact row_14290
  · exact row_14291
  · exact row_14292
  · exact row_14293
  · exact row_14294
  · exact row_14295
  · exact row_14296
  · exact row_14297
  · exact row_14298
  · exact row_14299
  · exact row_14300
  · exact row_14301
  · exact row_14302
  · exact row_14303
  · exact row_14304
  · exact row_14305
  · exact row_14306
  · exact row_14307
  · exact row_14308
  · exact row_14309
  · exact row_14310
  · exact row_14311

end BstLean.Part271.R3.Rows14237
