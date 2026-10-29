import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15452–15526. -/
namespace BstLean.Part271.R3.Rows15452
open Real BstLean.Part130 BstLean.Part227

theorem width_15452 : mW 15452 = 458613091794860 := by
  have hu : mW 15452 ≤ 458613091794860 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15452 ≤ 458613091794859 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15452 : RowArithmetic 15452 (1085039210406540346549/1000000000000000000000000) (148587120351023582706903/250000000000000000000000) (5659770451910867/1000000000000000000000000) where
  r0 := (52062252097/100000000000000000)
  k0 := (852786364794823/250000000000000000)
  k6 := (2203120654004559/200000000000000000)
  q := (175795335546765859007/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15452]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15452]

theorem width_15453 : mW 15453 = 458716979684767 := by
  have hu : mW 15453 ≤ 458716979684767 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15453 ≤ 458716979684766 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15453 : RowArithmetic 15453 (1085016609526609864659/1000000000000000000000000) (148584781810298502958297/250000000000000000000000) (5658819984475571/1000000000000000000000000) where
  r0 := (20822879429/40000000000000000)
  k0 := (26648280471899/7812500000000000)
  k6 := (1101524684144947/100000000000000000)
  q := (175801023887803338357/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15453]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15453]

theorem width_15454 : mW 15454 = 458820884383109 := by
  have hu : mW 15454 ≤ 458820884383109 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15454 ≤ 458820884383108 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15454 : RowArithmetic 15454 (1084994013529533205261/1000000000000000000000000) (118865954853133828644323/200000000000000000000000) (1131573948036823/200000000000000000000000) where
  r0 := (260260729327/500000000000000000)
  k0 := (3410814360371567/1000000000000000000)
  k6 := (11014890447472463/1000000000000000000)
  q := (87903356022395413433/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15454]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15454]

theorem width_15455 : mW 15455 = 458924805891516 := by
  have hu : mW 15455 ≤ 458924805891516 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15455 ≤ 458924805891515 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15455 : RowArithmetic 15455 (1084971422413929576019/1000000000000000000000000) (594320422477278776918371/1000000000000000000000000) (1414229929742313/250000000000000000000000) where
  r0 := (520470939757/1000000000000000000)
  k0 := (1705324419543753/500000000000000000)
  k6 := (11014534088086179/1000000000000000000)
  q := (175812400017746188551/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15455]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15455]

theorem width_15456 : mW 15456 = 459028744211620 := by
  have hu : mW 15456 ≤ 459028744211620 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15456 ≤ 459028744211619 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15456 : RowArithmetic 15456 (216989767235683605161/200000000000000000000000) (297155535937891076479893/500000000000000000000000) (1131193984152747/200000000000000000000000) where
  r0 := (520420429031/1000000000000000000)
  k0 := (3410483336543789/1000000000000000000)
  k6 := (5507088881642511/500000000000000000)
  q := (87909043903343642269/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15456]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15456]

theorem width_15457 : mW 15457 = 459132699345054 := by
  have hu : mW 15457 ≤ 459132699345054 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15457 ≤ 459132699345053 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15457 : RowArithmetic 15457 (135615781852702221829/125000000000000000000000) (594301722460938400245059/1000000000000000000000000) (5655020345500331/1000000000000000000000000) where
  r0 := (20814797059/40000000000000000)
  k0 := (1705158926369933/500000000000000000)
  k6 := (5506910736531699/500000000000000000)
  q := (175823775411631973067/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15457]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15457]

theorem width_15458 : mW 15458 = 459236671293449 := by
  have hu : mW 15458 ≤ 459236671293449 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15458 ≤ 459236671293448 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15458 : RowArithmetic 15458 (542451839171074600223/500000000000000000000000) (297146187116253414929939/500000000000000000000000) (5654070993111857/1000000000000000000000000) where
  r0 := (104063886417/200000000000000000)
  k0 := (42626904845817/12500000000000000)
  k6 := (2202693043483143/200000000000000000)
  q := (10989341427037381843/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15458]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15458]

theorem width_15459 : mW 15459 = 459340660058436 := by
  have hu : mW 15459 ≤ 459340660058436 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15459 ≤ 459340660058435 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15459 : RowArithmetic 15459 (542440553369316590147/500000000000000000000000) (74285378398780842378167/125000000000000000000000) (1130624372706231/200000000000000000000000) where
  r0 := (260134472931/500000000000000000)
  k0 := (53281045958223/15625000000000000)
  k6 := (11013108996336381/1000000000000000000)
  q := (175835150069603546263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15459]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15459]

theorem width_15460 : mW 15460 = 459444665641648 := by
  have hu : mW 15460 ≤ 459444665641648 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15460 ≤ 459444665641647 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15460 : RowArithmetic 15460 (1084858540009690432983/1000000000000000000000000) (148568420333479398447869/250000000000000000000000) (5652172956691067/1000000000000000000000000) where
  r0 := (520218467803/1000000000000000000)
  k0 := (1704910756857749/500000000000000000)
  k6 := (11012752809819807/1000000000000000000)
  q := (21980104640333266621/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15460]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15460]

theorem width_15461 : mW 15461 = 459548688044717 := by
  have hu : mW 15461 ≤ 459548688044717 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15461 ≤ 459548688044716 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15461 : RowArithmetic 15461 (33901124317310703293/31250000000000000000000) (594264336663278808063743/1000000000000000000000000) (5651224272524473/1000000000000000000000000) where
  r0 := (104033599581/200000000000000000)
  k0 := (3409656104825933/1000000000000000000)
  k6 := (2753099164465101/250000000000000000)
  q := (175846523991803716291/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15461]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15461]

theorem width_15462 : mW 15462 = 459652727269274 := by
  have hu : mW 15462 ≤ 459652727269274 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15462 ≤ 459652727269273 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15462 : RowArithmetic 15462 (135601677646251471443/125000000000000000000000) (4754039945424719964281/8000000000000000000000) (1412568952741073/250000000000000000000000) where
  r0 := (65014692021/125000000000000000)
  k0 := (34094907146603/10000000000000000)
  k6 := (11012040540452583/1000000000000000000)
  q := (175852210677034140037/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15462]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15462]

theorem width_15463 : mW 15463 = 459756783316952 := by
  have hu : mW 15463 ≤ 459756783316952 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15463 ≤ 459756783316951 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15463 : RowArithmetic 15463 (542395434528260223677/500000000000000000000000) (297122825439055352203077/500000000000000000000000) (2824663785971721/500000000000000000000000) where
  r0 := (520067082589/1000000000000000000)
  k0 := (3409325343211491/1000000000000000000)
  k6 := (11011684457590759/1000000000000000000)
  q := (175857897178375245123/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15463]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15463]

theorem width_15464 : mW 15464 = 459860856189382 := by
  have hu : mW 15464 ≤ 459860856189382 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15464 ≤ 459860856189381 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15464 : RowArithmetic 15464 (271192080453022975931/250000000000000000000000) (118847261952620129463937/200000000000000000000000) (5648379555394893/1000000000000000000000000) where
  r0 := (520016637167/1000000000000000000)
  k0 := (3409159990478953/1000000000000000000)
  k6 := (11011328409269347/1000000000000000000)
  q := (10991473968490304349/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15464]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15464]

theorem width_15465 : mW 15465 = 459964945888197 := by
  have hu : mW 15465 ≤ 459964945888197 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15465 ≤ 459964945888196 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15465 : RowArithmetic 15465 (1084745779435349353397/1000000000000000000000000) (594226969832819556895393/1000000000000000000000000) (5647431761251613/1000000000000000000000000) where
  r0 := (519966199899/1000000000000000000)
  k0 := (3408994656455573/1000000000000000000)
  k6 := (11010972395482763/1000000000000000000)
  q := (175869269629460848569/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15465]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15465]

theorem width_15466 : mW 15466 = 460069052415029 := by
  have hu : mW 15466 ≤ 460069052415029 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15466 ≤ 460069052415028 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15466 : RowArithmetic 15466 (108472324192491683539/100000000000000000000000) (594217631087027300633473/1000000000000000000000000) (5646484189446609/1000000000000000000000000) where
  r0 := (16247367837/31250000000000000)
  k0 := (3408829341140797/1000000000000000000)
  k6 := (440424656649017/40000000000000000)
  q := (87937477789620507173/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15466]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15466]

theorem width_15467 : mW 15467 = 460173175771510 := by
  have hu : mW 15467 ≤ 460173175771510 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15467 ≤ 460173175771509 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15467 : RowArithmetic 15467 (21694014185588377729/20000000000000000000000) (594208293525483649661977/1000000000000000000000000) (2822768419956457/500000000000000000000000) where
  r0 := (25993267491/50000000000000000)
  k0 := (340866404453079/100000000000000000)
  k6 := (11010260471491751/1000000000000000000)
  q := (1758806413452031963/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15467]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15467]

theorem width_15468 : mW 15468 = 460277315959273 := by
  have hu : mW 15468 ≤ 460277315959273 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15468 ≤ 460277315959272 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15468 : RowArithmetic 15468 (135584772687185026657/125000000000000000000000) (297099478573974315383587/500000000000000000000000) (1411147428145893/250000000000000000000000) where
  r0 := (103962987401/200000000000000000)
  k0 := (681699753324343/200000000000000000)
  k6 := (5504952280638081/500000000000000000)
  q := (175886326927365220933/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15468]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15468]

theorem width_15469 : mW 15469 = 460381472979949 := by
  have hu : mW 15469 ≤ 460381472979949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15469 ≤ 460381472979948 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15469 : RowArithmetic 15469 (216931131715545335027/200000000000000000000000) (118837924390836444004429/200000000000000000000000) (5643642807391679/1000000000000000000000000) where
  r0 := (519764532337/1000000000000000000)
  k0 := (426041688426217/125000000000000000)
  k6 := (5504774342786539/500000000000000000)
  q := (175892012325744911867/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15469]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15469]

theorem width_15470 : mW 15470 = 460485646835172 := by
  have hu : mW 15470 ≤ 460485646835172 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15470 ≤ 460485646835171 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15470 : RowArithmetic 15470 (1084633140518783645989/1000000000000000000000000) (594180287943944519480533/1000000000000000000000000) (5642696124270319/1000000000000000000000000) where
  r0 := (103942827163/200000000000000000)
  k0 := (1704084133447147/500000000000000000)
  k6 := (11009192844376923/1000000000000000000)
  q := (175897697540360089843/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15470]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15470]

theorem width_15471 : mW 15471 = 460589837526573 := by
  have hu : mW 15471 ≤ 460589837526573 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15471 ≤ 460589837526572 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15471 : RowArithmetic 15471 (1084610627319277979101/1000000000000000000000000) (594170955116995643814799/1000000000000000000000000) (1410437415788159/250000000000000000000000) where
  r0 := (519663747437/1000000000000000000)
  k0 := (3408003045071549/1000000000000000000)
  k6 := (275220925942053/25000000000000000)
  q := (175903382571228572723/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15471]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15471]

theorem width_15472 : mW 15472 = 460694045055785 := by
  have hu : mW 15472 ≤ 460694045055785 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15472 ≤ 460694045055784 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15472 : RowArithmetic 15472 (1084588118977836369681/1000000000000000000000000) (594161623473095836630257/1000000000000000000000000) (5640803423971777/1000000000000000000000000) where
  r0 := (649516709/1250000000000000)
  k0 := (681567568386877/200000000000000000)
  k6 := (5504240632741547/500000000000000000)
  q := (1374289589206001371/7812500000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15472]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15472]

theorem width_15473 : mW 15473 = 460798269424440 := by
  have hu : mW 15473 ≤ 460798269424440 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15473 ≤ 460798269424439 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15473 : RowArithmetic 15473 (13557070193663579209/12500000000000000000000) (74269036626500671287887/125000000000000000000000) (2819928703330463/500000000000000000000000) where
  r0 := (519562995103/1000000000000000000)
  k0 := (3407672657482237/1000000000000000000)
  k6 := (11008125527774271/1000000000000000000)
  q := (175914752081796710243/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15473]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15473]

theorem width_15474 : mW 15474 = 460902510634172 := by
  have hu : mW 15474 ≤ 460902510634172 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15474 ≤ 460902510634171 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15474 : RowArithmetic 15474 (542271558431827620827/500000000000000000000000) (594142963733484566586153/1000000000000000000000000) (1409727902788317/250000000000000000000000) where
  r0 := (64939078893/125000000000000000)
  k0 := (1703753745855633/500000000000000000)
  k6 := (11007769824550081/1000000000000000000)
  q := (43980109140382996553/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15474]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15474]

theorem width_15475 : mW 15475 = 461006768686613 := by
  have hu : mW 15475 ≤ 461006768686613 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15475 ≤ 461006768686612 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15475 : RowArithmetic 15475 (1084520623088171596187/1000000000000000000000000) (297066817818646951346333/500000000000000000000000) (1127593207476407/200000000000000000000000) where
  r0 := (519462275321/1000000000000000000)
  k0 := (851835586154407/250000000000000000)
  k6 := (220148283116099/20000000000000000)
  q := (87963060428795904873/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15475]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15475]

theorem width_15476 : mW 15476 = 461111043583395 := by
  have hu : mW 15476 ≤ 461111043583395 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15476 ≤ 461111043583394 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15476 : RowArithmetic 15476 (542249067082632203833/500000000000000000000000) (118824861744638754521593/200000000000000000000000) (5637020685280487/1000000000000000000000000) where
  r0 := (32463245477/62500000000000000)
  k0 := (3407177216197479/1000000000000000000)
  k6 := (11007058521533309/1000000000000000000)
  q := (35186360993998796863/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15476]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15476]

theorem width_15477 : mW 15477 = 461215335326152 := by
  have hu : mW 15477 ≤ 461215335326152 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15477 ≤ 461215335326151 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15477 : RowArithmetic 15477 (542237825046781262961/500000000000000000000000) (594114982990944814117687/1000000000000000000000000) (2818037777390943/500000000000000000000000) where
  r0 := (519361588077/1000000000000000000)
  k0 := (681402421290707/200000000000000000)
  k6 := (11006702921729591/1000000000000000000)
  q := (35187497779751262103/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15477]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15477]

theorem width_15478 : mW 15478 = 461319643916516 := by
  have hu : mW 15478 ≤ 461319643916516 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15478 ≤ 461319643916515 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15478 : RowArithmetic 15478 (8675625366973567597/8000000000000000000000) (594105658440307543493067/1000000000000000000000000) (5635130645819539/1000000000000000000000000) where
  r0 := (519311256651/1000000000000000000)
  k0 := (340684701537211/100000000000000000)
  k6 := (11006347356388227/1000000000000000000)
  q := (43985793160974146517/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15478]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15478]

theorem width_15479 : mW 15479 = 461423969356120 := by
  have hu : mW 15479 ≤ 461423969356120 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15479 ≤ 461423969356119 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15479 : RowArithmetic 15479 (542215348249147423087/500000000000000000000000) (148524083767760673199789/250000000000000000000000) (5634185958326769/1000000000000000000000000) where
  r0 := (103852186671/200000000000000000)
  k0 := (1703340971479599/500000000000000000)
  k6 := (11005991825503651/1000000000000000000)
  q := (175948856205432605819/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15479]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15479]

theorem width_15480 : mW 15480 = 461528311646597 := by
  have hu : mW 15480 ≤ 461528311646597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15480 ≤ 461528311646596 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15480 : RowArithmetic 15480 (1084408226971989878171/1000000000000000000000000) (594087012882911024294829/1000000000000000000000000) (225329659689477/40000000000000000000000) where
  r0 := (259605309093/500000000000000000)
  k0 := (340651688920767/100000000000000000)
  k6 := (5502818164535149/500000000000000000)
  q := (175954539583382161741/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15480]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15480]

theorem width_15481 : mW 15481 = 461632670789579 := by
  have hu : mW 15481 ≤ 461632670789579 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15481 ≤ 461632670789578 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15481 : RowArithmetic 15481 (67774110143213283073/62500000000000000000000) (118815538375134656352117/200000000000000000000000) (5632297247483391/1000000000000000000000000) where
  r0 := (259580155571/500000000000000000)
  k0 := (42579398176421/12500000000000000)
  k6 := (5502640433541303/500000000000000000)
  q := (43990055694440760733/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15481]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15481]

theorem width_15482 : mW 15482 = 461737046786701 := by
  have hu : mW 15482 ≤ 461737046786701 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15482 ≤ 461737046786700 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15482 : RowArithmetic 15482 (54218165122759689971/50000000000000000000000) (594068372049090451318053/1000000000000000000000000) (281567661199977/50000000000000000000000) where
  r0 := (519110012221/1000000000000000000)
  k0 := (106443338677293/31250000000000000)
  k6 := (11004925439535011/1000000000000000000)
  q := (87982952894296517809/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15482]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15482]

theorem width_15483 : mW 15483 = 461841439639594 := by
  have hu : mW 15483 ≤ 461841439639594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15483 ≤ 461841439639593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15483 : RowArithmetic 15483 (1084340847461966487579/1000000000000000000000000) (297029526701461688433389/500000000000000000000000) (5630409421718821/1000000000000000000000000) where
  r0 := (519059721421/1000000000000000000)
  k0 := (3406021839882909/1000000000000000000)
  k6 := (11004570046421953/1000000000000000000)
  q := (175971588615889923153/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15483]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15483]

theorem width_15484 : mW 15484 = 461945849349893 := by
  have hu : mW 15484 ≤ 461945849349893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15484 ≤ 461945849349892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15484 : RowArithmetic 15484 (542159198655181291591/500000000000000000000000) (74256216992116639385553/125000000000000000000000) (87960403758979/15625000000000000000000) where
  r0 := (259504719371/500000000000000000)
  k0 := (851464215186247/250000000000000000)
  k6 := (11004214687737871/1000000000000000000)
  q := (8798863562983574301/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15484]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15484]

theorem width_15485 : mW 15485 = 462050275919230 := by
  have hu : mW 15485 ≤ 462050275919230 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15485 ≤ 462050275919229 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15485 : RowArithmetic 15485 (1084295951999015547241/1000000000000000000000000) (148510104912720190058527/250000000000000000000000) (1407130620125133/250000000000000000000000) where
  r0 := (25947958209/50000000000000000)
  k0 := (3405691900249199/1000000000000000000)
  k6 := (1375482420434651/125000000000000000)
  q := (21997869214994437729/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15485]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15485]

theorem width_15486 : mW 15486 = 462154719349239 := by
  have hu : mW 15486 ≤ 462154719349239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15486 ≤ 462154719349238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15486 : RowArithmetic 15486 (542136755763279341689/500000000000000000000000) (594031104544527399771927/1000000000000000000000000) (2813789670714967/500000000000000000000000) where
  r0 := (259454448867/500000000000000000)
  k0 := (3405526958394971/1000000000000000000)
  k6 := (5501752036817203/500000000000000000)
  q := (175988635996759745329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15486]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15486]

theorem width_15487 : mW 15487 = 462259179641552 := by
  have hu : mW 15487 ≤ 462259179641552 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15487 ≤ 462259179641551 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15487 : RowArithmetic 15487 (271062768972906609941/250000000000000000000000) (594021790617634328140903/1000000000000000000000000) (2813318211648199/500000000000000000000000) where
  r0 := (518858639403/1000000000000000000)
  k0 := (340536203518173/100000000000000000)
  k6 := (11003148818203909/1000000000000000000)
  q := (5499822440315687137/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15487]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15487]

theorem width_15488 : mW 15488 = 462363656797803 := by
  have hu : mW 15488 ≤ 462363656797803 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15488 ≤ 462363656797802 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15488 : RowArithmetic 15488 (1084228645092853107213/1000000000000000000000000) (594012477869962734313853/1000000000000000000000000) (281284686301673/50000000000000000000000) where
  r0 := (518808389183/1000000000000000000)
  k0 := (3405197130599057/1000000000000000000)
  k6 := (5501396798590081/500000000000000000)
  q := 176
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15488]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15488]

theorem width_15489 : mW 15489 = 462468150819626 := by
  have hu : mW 15489 ≤ 462468150819626 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15489 ≤ 462468150819625 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15489 : RowArithmetic 15489 (1084206219128873470151/1000000000000000000000000) (594003166301274030368301/1000000000000000000000000) (5624751249574681/1000000000000000000000000) where
  r0 := (20750325883/40000000000000000)
  k0 := (1702516122326471/500000000000000000)
  k6 := (2750609602639403/250000000000000000)
  q := (35201136345294309263/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15489]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15489]

theorem width_15490 : mW 15490 = 462572661708654 := by
  have hu : mW 15490 ≤ 462572661708654 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15490 ≤ 462572661708653 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15490 : RowArithmetic 15490 (1084183797998323131263/1000000000000000000000000) (296996927955664792406971/500000000000000000000000) (281190449692683/50000000000000000000000) where
  r0 := (20748316523/40000000000000000)
  k0 := (851216844333241/250000000000000000)
  k6 := (5501041629165353/500000000000000000)
  q := (88005681634767195297/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15490]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15490]

theorem width_15491 : mW 15491 = 462677189466521 := by
  have hu : mW 15491 ≤ 462677189466521 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15491 ≤ 462677189466520 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15491 : RowArithmetic 15491 (1084161381699837861149/1000000000000000000000000) (296992273349945451872039/500000000000000000000000) (702858369850501/125000000000000000000000) where
  r0 := (518657687181/1000000000000000000)
  k0 := (3404702528635263/1000000000000000000)
  k6 := (5500864070246947/500000000000000000)
  q := (176017044629206293239/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15491]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15491]

theorem width_15492 : mW 15492 = 462781734094859 := by
  have hu : mW 15492 ≤ 462781734094859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15492 ≤ 462781734094858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15492 : RowArithmetic 15492 (1084138970232054572589/1000000000000000000000000) (593975238666719521924543/1000000000000000000000000) (2810962572179693/500000000000000000000000) where
  r0 := (518607469393/1000000000000000000)
  k0 := (680907539712509/200000000000000000)
  k6 := (5500686528520813/500000000000000000)
  q := (88011362902752505893/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15492]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15492]

theorem width_15493 : mW 15493 = 462886295595303 := by
  have hu : mW 15493 ≤ 462886295595303 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15493 ≤ 462886295595302 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15493 : RowArithmetic 15493 (1084116563593609696567/1000000000000000000000000) (593965931811577040972351/1000000000000000000000000) (2810491775226721/500000000000000000000000) where
  r0 := (129639314927/250000000000000000)
  k0 := (3404372887107669/1000000000000000000)
  k6 := (11001018007968353/1000000000000000000)
  q := (176028406798448300903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15493]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15493]

theorem width_15494 : mW 15494 = 462990873969487 := by
  have hu : mW 15494 ≤ 462990873969487 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15494 ≤ 462990873969486 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15494 : RowArithmetic 15494 (1084094161783140481401/1000000000000000000000000) (296978313067112566163941/500000000000000000000000) (702505272127483/125000000000000000000000) where
  r0 := (129626764531/250000000000000000)
  k0 := (3404208094266771/1000000000000000000)
  k6 := (11000662993268527/1000000000000000000)
  q := (35206817521610782479/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15494]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15494]

theorem width_15495 : mW 15495 = 463095469219043 := by
  have hu : mW 15495 ≤ 463095469219043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15495 ≤ 463095469219042 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15495 : RowArithmetic 15495 (1084071764799285316167/1000000000000000000000000) (593947321634425580003941/1000000000000000000000000) (5619101023992387/1000000000000000000000000) where
  r0 := (810088851/1562500000000000)
  k0 := (1702021660019637/500000000000000000)
  k6 := (2750077003234151/250000000000000000)
  q := (88019884117169797601/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15495]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15495]

theorem width_15496 : mW 15496 = 463200081345606 := by
  have hu : mW 15496 ≤ 463200081345606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15496 ≤ 463200081345605 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15496 : RowArithmetic 15496 (135506171580085263569/125000000000000000000000) (59393801831194013175023/100000000000000000000000) (1123632018260947/200000000000000000000000) where
  r0 := (518406679253/1000000000000000000)
  k0 := (3403878564418031/1000000000000000000)
  k6 := (5499976533483519/500000000000000000)
  q := (88022724338661547701/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15496]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15496]

theorem width_15497 : mW 15497 = 463304710350810 := by
  have hu : mW 15497 ≤ 463304710350810 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15497 ≤ 463304710350809 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15497 : RowArithmetic 15497 (1084026985305969582523/1000000000000000000000000) (593928716166530666975323/1000000000000000000000000) (5617219378890669/1000000000000000000000000) where
  r0 := (518356501963/1000000000000000000)
  k0 := (3403713827405743/1000000000000000000)
  k6 := (5499799077677143/500000000000000000)
  q := (88025564468511078103/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15497]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15497]

theorem width_15498 : mW 15498 = 463409356236288 := by
  have hu : mW 15498 ≤ 463409356236288 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15498 ≤ 463409356236287 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15498 : RowArithmetic 15498 (108400460279378727749/100000000000000000000000) (593919415197959199731567/1000000000000000000000000) (5616278886683987/1000000000000000000000000) where
  r0 := (259153166383/500000000000000000)
  k0 := (170177455449599/50000000000000000)
  k6 := (5499621639046403/500000000000000000)
  q := (11003550563340907373/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15498]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15498]

theorem width_15499 : mW 15499 = 463514019003675 := by
  have hu : mW 15499 ≤ 463514019003675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15499 ≤ 463514019003674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15499 : RowArithmetic 15499 (54199111255138728807/50000000000000000000000) (593910115405987665060103/1000000000000000000000000) (5615338614618489/1000000000000000000000000) where
  r0 := (518256171661/1000000000000000000)
  k0 := (3403384409176159/1000000000000000000)
  k6 := (343715263599283/31250000000000000)
  q := (7042499556265516727/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15499]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15499]

theorem width_15500 : mW 15500 = 463618698654603 := by
  have hu : mW 15500 ≤ 463618698654603 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15500 ≤ 463618698654602 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15500 : RowArithmetic 15500 (216791970446314464739/200000000000000000000000) (593900816790378128161719/1000000000000000000000000) (1122879712525607/200000000000000000000000) where
  r0 := (518206018647/1000000000000000000)
  k0 := (53175308249339/15625000000000000)
  k6 := (10998533626601497/1000000000000000000)
  q := (88034084308295045729/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15500]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15500]

theorem width_15501 : mW 15501 = 463723395190709 := by
  have hu : mW 15501 ≤ 463723395190709 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15501 ≤ 463723395190708 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15501 : RowArithmetic 15501 (1083937484178820237603/1000000000000000000000000) (148472879837723188015211/250000000000000000000000) (5613458730646449/1000000000000000000000000) where
  r0 := (259077936861/500000000000000000)
  k0 := (3403055065332723/1000000000000000000)
  k6 := (10998178852360591/1000000000000000000)
  q := (11004615508958048099/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15501]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15501]

theorem width_15502 : mW 15502 = 463828108613624 := by
  have hu : mW 15502 ≤ 463828108613624 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15502 ≤ 463828108613623 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15502 : RowArithmetic 15502 (541957560471580233931/500000000000000000000000) (7423527788591172246897/12500000000000000000000) (5612519118607653/1000000000000000000000000) where
  r0 := (518105736883/1000000000000000000)
  k0 := (425361302661761/125000000000000000)
  k6 := (10997824112448799/1000000000000000000)
  q := (88039763743435840731/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15502]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15502]

theorem width_15503 : mW 15503 = 463932838924984 := by
  have hu : mW 15503 ≤ 463932838924984 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15503 ≤ 463932838924983 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15503 : RowArithmetic 15503 (270973190630808509241/250000000000000000000000) (296936463999671705335087/500000000000000000000000) (1122315945289107/200000000000000000000000) where
  r0 := (518055608129/1000000000000000000)
  k0 := (850681448960301/250000000000000000)
  k6 := (10997469406860587/1000000000000000000)
  q := (176085206647236553141/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15503]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15503]

theorem width_15504 : mW 15504 = 464037586126423 := by
  have hu : mW 15504 ≤ 464037586126423 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15504 ≤ 464037586126422 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15504 : RowArithmetic 15504 (13548380111471038811/12500000000000000000000) (1855823856521262640609/3125000000000000000000) (561064055409403/100000000000000000000000) where
  r0 := (259002743729/500000000000000000)
  k0 := (17012805944851/5000000000000000)
  k6 := (549855736779521/50000000000000000)
  q := (176090885624441107813/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15504]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15504]

theorem width_15505 : mW 15505 = 464142350219575 := by
  have hu : mW 15505 ≤ 464142350219575 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15505 ≤ 464142350219574 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15505 : RowArithmetic 15505 (270962015031287580381/250000000000000000000000) (23754173653977522454987/40000000000000000000000) (2804850800743549/500000000000000000000000) where
  r0 := (129488843717/250000000000000000)
  k0 := (1701198300338603/500000000000000000)
  k6 := (10996760098632763/1000000000000000000)
  q := (176096564418503065809/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15505]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15505]

theorem width_15506 : mW 15506 = 464247131206073 := by
  have hu : mW 15506 ≤ 464247131206073 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15506 ≤ 464247131206072 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15506 : RowArithmetic 15506 (1083825716144279149447/1000000000000000000000000) (148461262446751974096719/250000000000000000000000) (350547679284921/62500000000000000000000) where
  r0 := (258952635179/500000000000000000)
  k0 := (3402232030961631/1000000000000000000)
  k6 := (5498202747991043/500000000000000000)
  q := (5503195094670004519/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15506]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15506]

theorem width_15507 : mW 15507 = 464351929087554 := by
  have hu : mW 15507 ≤ 464351929087554 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15507 ≤ 464351929087553 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15507 : RowArithmetic 15507 (1083803376973712248983/1000000000000000000000000) (148458939849819027706907/250000000000000000000000) (5607824355242919/1000000000000000000000000) where
  r0 := (20714206957/40000000000000000)
  k0 := (1701033739908159/500000000000000000)
  k6 := (1374506365954107/125000000000000000)
  q := (176107921457270058827/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15507]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15507]

theorem width_15508 : mW 15508 = 464456743865651 := by
  have hu : mW 15508 ≤ 464456743865651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15508 ≤ 464456743865650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15508 : RowArithmetic 15508 (135472630326511757739/125000000000000000000000) (593826470186005321932487/1000000000000000000000000) (2803443030736847/500000000000000000000000) where
  r0 := (517805085569/1000000000000000000)
  k0 := (1700951473621981/500000000000000000)
  k6 := (1374462049197443/125000000000000000)
  q := (176113599702010520231/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15508]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15508]

theorem width_15509 : mW 15509 = 464561575541997 := by
  have hu : mW 15509 ≤ 464561575541997 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15509 ≤ 464561575541996 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15509 : RowArithmetic 15509 (270939678264517379639/250000000000000000000000) (18556786942092443258211/31250000000000000000000) (1401486996796283/250000000000000000000000) where
  r0 := (258877502643/500000000000000000)
  k0 := (3401738433234117/1000000000000000000)
  k6 := (5497670946908311/500000000000000000)
  q := (5503727430114976179/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15509]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15509]

theorem width_15510 : mW 15510 = 464666424118229 := by
  have hu : mW 15510 ≤ 464666424118229 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15510 ≤ 464666424118228 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15510 : RowArithmetic 15510 (1083736388310282747787/1000000000000000000000000) (593807895281897432331861/1000000000000000000000000) (5605010132311283/1000000000000000000000000) where
  r0 := (20708197323/40000000000000000)
  k0 := (3401573937786191/1000000000000000000)
  k6 := (5497493714169281/500000000000000000)
  q := (176124955642293917371/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15510]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15510]

theorem width_15511 : mW 15511 = 464771289595981 := by
  have hu : mW 15511 ≤ 464771289595981 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15511 ≤ 464771289595980 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15511 : RowArithmetic 15511 (135464258545922416933/125000000000000000000000) (18556206549705808127619/31250000000000000000000) (1120814499357251/200000000000000000000000) where
  r0 := (258827434467/500000000000000000)
  k0 := (3401409460896307/1000000000000000000)
  k6 := (10994632997139839/1000000000000000000)
  q := (88065316668936131181/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15511]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15511]

theorem width_15512 : mW 15512 = 464876171976886 := by
  have hu : mW 15512 ≤ 464876171976886 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15512 ≤ 464876171976885 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15512 : RowArithmetic 15512 (1083691753228005677991/1000000000000000000000000) (296894662536393162600363/500000000000000000000000) (1120627016108839/200000000000000000000000) where
  r0 := (258802406431/500000000000000000)
  k0 := (340124500256387/100000000000000000)
  k6 := (10994278600214927/1000000000000000000)
  q := (176136310850431973047/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15512]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15512]

theorem width_15513 : mW 15513 = 464981071262580 := by
  have hu : mW 15513 ≤ 464981071262580 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15513 ≤ 464981071262579 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15513 : RowArithmetic 15513 (1083669442890807693167/1000000000000000000000000) (593780041728261752105377/1000000000000000000000000) (5602197883519239/1000000000000000000000000) where
  r0 := (517554764857/1000000000000000000)
  k0 := (3401080562785003/1000000000000000000)
  k6 := (343560132423697/31250000000000000)
  q := (176141988179990746919/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15513]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15513]

theorem width_15514 : mW 15514 = 465085987454698 := by
  have hu : mW 15514 ≤ 465085987454698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15514 ≤ 465085987454697 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15514 : RowArithmetic 15514 (216729427470886421921/200000000000000000000000) (593770759556775161391483/1000000000000000000000000) (1400315226411389/250000000000000000000000) where
  r0 := (129376181229/250000000000000000)
  k0 := (1700458070776269/500000000000000000)
  k6 := (5496784954582223/500000000000000000)
  q := (176147665326566278621/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15514]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15514]

theorem width_15515 : mW 15515 = 465190920554873 := by
  have hu : mW 15515 ≤ 465190920554873 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15515 ≤ 465190920554872 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15515 : RowArithmetic 15515 (1083624836617526787739/1000000000000000000000000) (148440369639522404934419/250000000000000000000000) (5600324146857369/1000000000000000000000000) where
  r0 := (517454693039/1000000000000000000)
  k0 := (1700375869434583/500000000000000000)
  k6 := (5496607807513917/500000000000000000)
  q := (176153342290176259943/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15515]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15515]

theorem width_15516 : mW 15516 = 465295870564742 := by
  have hu : mW 15516 ≤ 465295870564742 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15516 ≤ 465295870564741 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15516 : RowArithmetic 15516 (1083602540678738788087/1000000000000000000000000) (593752198731968197151523/1000000000000000000000000) (44795100856711/8000000000000000000000) where
  r0 := (517404669223/1000000000000000000)
  k0 := (3400587354727717/1000000000000000000)
  k6 := (5496430677571473/500000000000000000)
  q := (7046360762833535193/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15516]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15516]

theorem width_15517 : mW 15517 = 465400837485939 := by
  have hu : mW 15517 ≤ 465400837485939 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15517 ≤ 465400837485938 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15517 : RowArithmetic 15517 (1083580249536716624609/1000000000000000000000000) (593742920078174161436269/1000000000000000000000000) (5598451286274331/1000000000000000000000000) where
  r0 := (258677326733/500000000000000000)
  k0 := (3400422989124309/1000000000000000000)
  k6 := (5496253564752133/500000000000000000)
  q := (88082347834285162179/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15517]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15517]

theorem width_15518 : mW 15518 = 465505821320098 := by
  have hu : mW 15518 ≤ 465505821320098 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15518 ≤ 465505821320097 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15518 : RowArithmetic 15518 (135444745398763662281/125000000000000000000000) (296866821298235372727663/500000000000000000000000) (5597515184348021/1000000000000000000000000) where
  r0 := (258652322883/500000000000000000)
  k0 := (3400258642055057/1000000000000000000)
  k6 := (5496076469053137/500000000000000000)
  q := (88085186041694888391/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15518]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15518]

theorem width_15519 : mW 15519 = 465610822068855 := by
  have hu : mW 15519 ≤ 465610822068855 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15519 ≤ 465610822068854 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15519 : RowArithmetic 15519 (541767840818782826993/500000000000000000000000) (296862183143310614790291/500000000000000000000000) (5596579301244227/1000000000000000000000000) where
  r0 := (517254646123/1000000000000000000)
  k0 := (3400094313522649/1000000000000000000)
  k6 := (10991798780943457/1000000000000000000)
  q := (11011003019707151093/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15519]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15519]

theorem width_15520 : mW 15520 = 465715839733845 := by
  have hu : mW 15520 ≤ 465715839733845 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15520 ≤ 465715839733844 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15520 : RowArithmetic 15520 (1083513404877735345533/1000000000000000000000000) (296857545574194512076703/500000000000000000000000) (559564363689727/100000000000000000000000) where
  r0 := (517204654533/1000000000000000000)
  k0 := (212495625219789/62500000000000000)
  k6 := (10991444658010297/1000000000000000000)
  q := (176181724364361924019/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15520]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15520]

theorem width_15521 : mW 15521 = 465820874316703 := by
  have hu : mW 15521 ≤ 465820874316703 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15521 ≤ 465820874316702 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15521 : RowArithmetic 15521 (1083491132909268513379/1000000000000000000000000) (296852908590768827409661/500000000000000000000000) (1118941638248299/200000000000000000000000) where
  r0 := (129288667749/250000000000000000)
  k0 := (339976571203967/100000000000000000)
  k6 := (10991090569301283/1000000000000000000)
  q := (176187400230549971073/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15521]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15521]

theorem width_15522 : mW 15522 = 465925925819063 := by
  have hu : mW 15522 ≤ 465925925819063 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15522 ≤ 465925925819062 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15522 : RowArithmetic 15522 (1083468865730816105561/1000000000000000000000000) (118739308877166113303509/200000000000000000000000) (1398443241052821/250000000000000000000000) where
  r0 := (517104695509/1000000000000000000)
  k0 := (339960143908461/100000000000000000)
  k6 := (5495368257405451/500000000000000000)
  q := (176193075913896230499/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15522]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15522]

theorem width_15523 : mW 15523 = 466030994242562 := by
  have hu : mW 15523 ≤ 466030994242562 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15523 ≤ 466030994242561 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15523 : RowArithmetic 15523 (1083446603341028593343/1000000000000000000000000) (296843636380515667836801/500000000000000000000000) (2796418977870503/500000000000000000000000) where
  r0 := (51705472807/100000000000000000)
  k0 := (849859296161889/250000000000000000)
  k6 := (5495191247266821/500000000000000000)
  q := (88099375707209185649/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15523]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15523]

theorem width_15524 : mW 15524 = 466136079588835 := by
  have hu : mW 15524 ≤ 466136079588835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15524 ≤ 466136079588834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15524 : RowArithmetic 15524 (541712172869278788279/500000000000000000000000) (593678002306903673087649/1000000000000000000000000) (5591903165765081/1000000000000000000000000) where
  r0 := (258502384339/500000000000000000)
  k0 := (679854589745581/200000000000000000)
  k6 := (2198005701692799/200000000000000000)
  q := (17620442673213405963/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15524]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15524]

theorem width_15525 : mW 15525 = 466241181859516 := by
  have hu : mW 15525 ≤ 466241181859516 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15525 ≤ 466241181859515 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15525 : RowArithmetic 15525 (270850523230513865387/250000000000000000000000) (23746749320928451005671/40000000000000000000000) (1397742148554491/250000000000000000000000) where
  r0 := (516954817331/1000000000000000000)
  k0 := (849777182830441/250000000000000000)
  k6 := (10989674556596451/1000000000000000000)
  q := (35242020373412191761/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15525]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15525]

theorem width_15526 : mW 15526 = 466346301056241 := by
  have hu : mW 15526 ≤ 466346301056241 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15526 ≤ 466346301056240 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15526 : RowArithmetic 15526 (1083379844890174498793/1000000000000000000000000) (593659464909717904849807/1000000000000000000000000) (43672142508079/7812500000000000000000) where
  r0 := (516904874027/1000000000000000000)
  k0 := (3398944532425243/1000000000000000000)
  k6 := (5494660319462751/500000000000000000)
  q := (176215776819216729293/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15526]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15526]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15452 then ⟨(1085039210406540346549/1000000000000000000000000), (148587120351023582706903/250000000000000000000000), (5659770451910867/1000000000000000000000000)⟩ else
  if n = 15453 then ⟨(1085016609526609864659/1000000000000000000000000), (148584781810298502958297/250000000000000000000000), (5658819984475571/1000000000000000000000000)⟩ else
  if n = 15454 then ⟨(1084994013529533205261/1000000000000000000000000), (118865954853133828644323/200000000000000000000000), (1131573948036823/200000000000000000000000)⟩ else
  if n = 15455 then ⟨(1084971422413929576019/1000000000000000000000000), (594320422477278776918371/1000000000000000000000000), (1414229929742313/250000000000000000000000)⟩ else
  if n = 15456 then ⟨(216989767235683605161/200000000000000000000000), (297155535937891076479893/500000000000000000000000), (1131193984152747/200000000000000000000000)⟩ else
  if n = 15457 then ⟨(135615781852702221829/125000000000000000000000), (594301722460938400245059/1000000000000000000000000), (5655020345500331/1000000000000000000000000)⟩ else
  if n = 15458 then ⟨(542451839171074600223/500000000000000000000000), (297146187116253414929939/500000000000000000000000), (5654070993111857/1000000000000000000000000)⟩ else
  if n = 15459 then ⟨(542440553369316590147/500000000000000000000000), (74285378398780842378167/125000000000000000000000), (1130624372706231/200000000000000000000000)⟩ else
  if n = 15460 then ⟨(1084858540009690432983/1000000000000000000000000), (148568420333479398447869/250000000000000000000000), (5652172956691067/1000000000000000000000000)⟩ else
  if n = 15461 then ⟨(33901124317310703293/31250000000000000000000), (594264336663278808063743/1000000000000000000000000), (5651224272524473/1000000000000000000000000)⟩ else
  if n = 15462 then ⟨(135601677646251471443/125000000000000000000000), (4754039945424719964281/8000000000000000000000), (1412568952741073/250000000000000000000000)⟩ else
  if n = 15463 then ⟨(542395434528260223677/500000000000000000000000), (297122825439055352203077/500000000000000000000000), (2824663785971721/500000000000000000000000)⟩ else
  if n = 15464 then ⟨(271192080453022975931/250000000000000000000000), (118847261952620129463937/200000000000000000000000), (5648379555394893/1000000000000000000000000)⟩ else
  if n = 15465 then ⟨(1084745779435349353397/1000000000000000000000000), (594226969832819556895393/1000000000000000000000000), (5647431761251613/1000000000000000000000000)⟩ else
  if n = 15466 then ⟨(108472324192491683539/100000000000000000000000), (594217631087027300633473/1000000000000000000000000), (5646484189446609/1000000000000000000000000)⟩ else
  if n = 15467 then ⟨(21694014185588377729/20000000000000000000000), (594208293525483649661977/1000000000000000000000000), (2822768419956457/500000000000000000000000)⟩ else
  if n = 15468 then ⟨(135584772687185026657/125000000000000000000000), (297099478573974315383587/500000000000000000000000), (1411147428145893/250000000000000000000000)⟩ else
  if n = 15469 then ⟨(216931131715545335027/200000000000000000000000), (118837924390836444004429/200000000000000000000000), (5643642807391679/1000000000000000000000000)⟩ else
  if n = 15470 then ⟨(1084633140518783645989/1000000000000000000000000), (594180287943944519480533/1000000000000000000000000), (5642696124270319/1000000000000000000000000)⟩ else
  if n = 15471 then ⟨(1084610627319277979101/1000000000000000000000000), (594170955116995643814799/1000000000000000000000000), (1410437415788159/250000000000000000000000)⟩ else
  if n = 15472 then ⟨(1084588118977836369681/1000000000000000000000000), (594161623473095836630257/1000000000000000000000000), (5640803423971777/1000000000000000000000000)⟩ else
  if n = 15473 then ⟨(13557070193663579209/12500000000000000000000), (74269036626500671287887/125000000000000000000000), (2819928703330463/500000000000000000000000)⟩ else
  if n = 15474 then ⟨(542271558431827620827/500000000000000000000000), (594142963733484566586153/1000000000000000000000000), (1409727902788317/250000000000000000000000)⟩ else
  if n = 15475 then ⟨(1084520623088171596187/1000000000000000000000000), (297066817818646951346333/500000000000000000000000), (1127593207476407/200000000000000000000000)⟩ else
  if n = 15476 then ⟨(542249067082632203833/500000000000000000000000), (118824861744638754521593/200000000000000000000000), (5637020685280487/1000000000000000000000000)⟩ else
  if n = 15477 then ⟨(542237825046781262961/500000000000000000000000), (594114982990944814117687/1000000000000000000000000), (2818037777390943/500000000000000000000000)⟩ else
  if n = 15478 then ⟨(8675625366973567597/8000000000000000000000), (594105658440307543493067/1000000000000000000000000), (5635130645819539/1000000000000000000000000)⟩ else
  if n = 15479 then ⟨(542215348249147423087/500000000000000000000000), (148524083767760673199789/250000000000000000000000), (5634185958326769/1000000000000000000000000)⟩ else
  if n = 15480 then ⟨(1084408226971989878171/1000000000000000000000000), (594087012882911024294829/1000000000000000000000000), (225329659689477/40000000000000000000000)⟩ else
  if n = 15481 then ⟨(67774110143213283073/62500000000000000000000), (118815538375134656352117/200000000000000000000000), (5632297247483391/1000000000000000000000000)⟩ else
  if n = 15482 then ⟨(54218165122759689971/50000000000000000000000), (594068372049090451318053/1000000000000000000000000), (281567661199977/50000000000000000000000)⟩ else
  if n = 15483 then ⟨(1084340847461966487579/1000000000000000000000000), (297029526701461688433389/500000000000000000000000), (5630409421718821/1000000000000000000000000)⟩ else
  if n = 15484 then ⟨(542159198655181291591/500000000000000000000000), (74256216992116639385553/125000000000000000000000), (87960403758979/15625000000000000000000)⟩ else
  if n = 15485 then ⟨(1084295951999015547241/1000000000000000000000000), (148510104912720190058527/250000000000000000000000), (1407130620125133/250000000000000000000000)⟩ else
  if n = 15486 then ⟨(542136755763279341689/500000000000000000000000), (594031104544527399771927/1000000000000000000000000), (2813789670714967/500000000000000000000000)⟩ else
  if n = 15487 then ⟨(271062768972906609941/250000000000000000000000), (594021790617634328140903/1000000000000000000000000), (2813318211648199/500000000000000000000000)⟩ else
  if n = 15488 then ⟨(1084228645092853107213/1000000000000000000000000), (594012477869962734313853/1000000000000000000000000), (281284686301673/50000000000000000000000)⟩ else
  if n = 15489 then ⟨(1084206219128873470151/1000000000000000000000000), (594003166301274030368301/1000000000000000000000000), (5624751249574681/1000000000000000000000000)⟩ else
  if n = 15490 then ⟨(1084183797998323131263/1000000000000000000000000), (296996927955664792406971/500000000000000000000000), (281190449692683/50000000000000000000000)⟩ else
  if n = 15491 then ⟨(1084161381699837861149/1000000000000000000000000), (296992273349945451872039/500000000000000000000000), (702858369850501/125000000000000000000000)⟩ else
  if n = 15492 then ⟨(1084138970232054572589/1000000000000000000000000), (593975238666719521924543/1000000000000000000000000), (2810962572179693/500000000000000000000000)⟩ else
  if n = 15493 then ⟨(1084116563593609696567/1000000000000000000000000), (593965931811577040972351/1000000000000000000000000), (2810491775226721/500000000000000000000000)⟩ else
  if n = 15494 then ⟨(1084094161783140481401/1000000000000000000000000), (296978313067112566163941/500000000000000000000000), (702505272127483/125000000000000000000000)⟩ else
  if n = 15495 then ⟨(1084071764799285316167/1000000000000000000000000), (593947321634425580003941/1000000000000000000000000), (5619101023992387/1000000000000000000000000)⟩ else
  if n = 15496 then ⟨(135506171580085263569/125000000000000000000000), (59393801831194013175023/100000000000000000000000), (1123632018260947/200000000000000000000000)⟩ else
  if n = 15497 then ⟨(1084026985305969582523/1000000000000000000000000), (593928716166530666975323/1000000000000000000000000), (5617219378890669/1000000000000000000000000)⟩ else
  if n = 15498 then ⟨(108400460279378727749/100000000000000000000000), (593919415197959199731567/1000000000000000000000000), (5616278886683987/1000000000000000000000000)⟩ else
  if n = 15499 then ⟨(54199111255138728807/50000000000000000000000), (593910115405987665060103/1000000000000000000000000), (5615338614618489/1000000000000000000000000)⟩ else
  if n = 15500 then ⟨(216791970446314464739/200000000000000000000000), (593900816790378128161719/1000000000000000000000000), (1122879712525607/200000000000000000000000)⟩ else
  if n = 15501 then ⟨(1083937484178820237603/1000000000000000000000000), (148472879837723188015211/250000000000000000000000), (5613458730646449/1000000000000000000000000)⟩ else
  if n = 15502 then ⟨(541957560471580233931/500000000000000000000000), (7423527788591172246897/12500000000000000000000), (5612519118607653/1000000000000000000000000)⟩ else
  if n = 15503 then ⟨(270973190630808509241/250000000000000000000000), (296936463999671705335087/500000000000000000000000), (1122315945289107/200000000000000000000000)⟩ else
  if n = 15504 then ⟨(13548380111471038811/12500000000000000000000), (1855823856521262640609/3125000000000000000000), (561064055409403/100000000000000000000000)⟩ else
  if n = 15505 then ⟨(270962015031287580381/250000000000000000000000), (23754173653977522454987/40000000000000000000000), (2804850800743549/500000000000000000000000)⟩ else
  if n = 15506 then ⟨(1083825716144279149447/1000000000000000000000000), (148461262446751974096719/250000000000000000000000), (350547679284921/62500000000000000000000)⟩ else
  if n = 15507 then ⟨(1083803376973712248983/1000000000000000000000000), (148458939849819027706907/250000000000000000000000), (5607824355242919/1000000000000000000000000)⟩ else
  if n = 15508 then ⟨(135472630326511757739/125000000000000000000000), (593826470186005321932487/1000000000000000000000000), (2803443030736847/500000000000000000000000)⟩ else
  if n = 15509 then ⟨(270939678264517379639/250000000000000000000000), (18556786942092443258211/31250000000000000000000), (1401486996796283/250000000000000000000000)⟩ else
  if n = 15510 then ⟨(1083736388310282747787/1000000000000000000000000), (593807895281897432331861/1000000000000000000000000), (5605010132311283/1000000000000000000000000)⟩ else
  if n = 15511 then ⟨(135464258545922416933/125000000000000000000000), (18556206549705808127619/31250000000000000000000), (1120814499357251/200000000000000000000000)⟩ else
  if n = 15512 then ⟨(1083691753228005677991/1000000000000000000000000), (296894662536393162600363/500000000000000000000000), (1120627016108839/200000000000000000000000)⟩ else
  if n = 15513 then ⟨(1083669442890807693167/1000000000000000000000000), (593780041728261752105377/1000000000000000000000000), (5602197883519239/1000000000000000000000000)⟩ else
  if n = 15514 then ⟨(216729427470886421921/200000000000000000000000), (593770759556775161391483/1000000000000000000000000), (1400315226411389/250000000000000000000000)⟩ else
  if n = 15515 then ⟨(1083624836617526787739/1000000000000000000000000), (148440369639522404934419/250000000000000000000000), (5600324146857369/1000000000000000000000000)⟩ else
  if n = 15516 then ⟨(1083602540678738788087/1000000000000000000000000), (593752198731968197151523/1000000000000000000000000), (44795100856711/8000000000000000000000)⟩ else
  if n = 15517 then ⟨(1083580249536716624609/1000000000000000000000000), (593742920078174161436269/1000000000000000000000000), (5598451286274331/1000000000000000000000000)⟩ else
  if n = 15518 then ⟨(135444745398763662281/125000000000000000000000), (296866821298235372727663/500000000000000000000000), (5597515184348021/1000000000000000000000000)⟩ else
  if n = 15519 then ⟨(541767840818782826993/500000000000000000000000), (296862183143310614790291/500000000000000000000000), (5596579301244227/1000000000000000000000000)⟩ else
  if n = 15520 then ⟨(1083513404877735345533/1000000000000000000000000), (296857545574194512076703/500000000000000000000000), (559564363689727/100000000000000000000000)⟩ else
  if n = 15521 then ⟨(1083491132909268513379/1000000000000000000000000), (296852908590768827409661/500000000000000000000000), (1118941638248299/200000000000000000000000)⟩ else
  if n = 15522 then ⟨(1083468865730816105561/1000000000000000000000000), (118739308877166113303509/200000000000000000000000), (1398443241052821/250000000000000000000000)⟩ else
  if n = 15523 then ⟨(1083446603341028593343/1000000000000000000000000), (296843636380515667836801/500000000000000000000000), (2796418977870503/500000000000000000000000)⟩ else
  if n = 15524 then ⟨(541712172869278788279/500000000000000000000000), (593678002306903673087649/1000000000000000000000000), (5591903165765081/1000000000000000000000000)⟩ else
  if n = 15525 then ⟨(270850523230513865387/250000000000000000000000), (23746749320928451005671/40000000000000000000000), (1397742148554491/250000000000000000000000)⟩ else
  ⟨(1083379844890174498793/1000000000000000000000000), (593659464909717904849807/1000000000000000000000000), (43672142508079/7812500000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15452 ≤ n) (hb : n ≤ 15526) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15452
  · exact row_15453
  · exact row_15454
  · exact row_15455
  · exact row_15456
  · exact row_15457
  · exact row_15458
  · exact row_15459
  · exact row_15460
  · exact row_15461
  · exact row_15462
  · exact row_15463
  · exact row_15464
  · exact row_15465
  · exact row_15466
  · exact row_15467
  · exact row_15468
  · exact row_15469
  · exact row_15470
  · exact row_15471
  · exact row_15472
  · exact row_15473
  · exact row_15474
  · exact row_15475
  · exact row_15476
  · exact row_15477
  · exact row_15478
  · exact row_15479
  · exact row_15480
  · exact row_15481
  · exact row_15482
  · exact row_15483
  · exact row_15484
  · exact row_15485
  · exact row_15486
  · exact row_15487
  · exact row_15488
  · exact row_15489
  · exact row_15490
  · exact row_15491
  · exact row_15492
  · exact row_15493
  · exact row_15494
  · exact row_15495
  · exact row_15496
  · exact row_15497
  · exact row_15498
  · exact row_15499
  · exact row_15500
  · exact row_15501
  · exact row_15502
  · exact row_15503
  · exact row_15504
  · exact row_15505
  · exact row_15506
  · exact row_15507
  · exact row_15508
  · exact row_15509
  · exact row_15510
  · exact row_15511
  · exact row_15512
  · exact row_15513
  · exact row_15514
  · exact row_15515
  · exact row_15516
  · exact row_15517
  · exact row_15518
  · exact row_15519
  · exact row_15520
  · exact row_15521
  · exact row_15522
  · exact row_15523
  · exact row_15524
  · exact row_15525
  · exact row_15526

end BstLean.Part271.R3.Rows15452
