import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15377–15451. -/
namespace BstLean.Part271.R3.Rows15377
open Real BstLean.Part130 BstLean.Part227

theorem width_15377 : mW 15377 = 450869284813560 := by
  have hu : mW 15377 ≤ 450869284813560 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15377 ≤ 450869284813559 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15377 : RowArithmetic 15377 (1086748294271959502673/1000000000000000000000000) (595053445361725785663493/1000000000000000000000000) (2865848212828139/500000000000000000000000) where
  r0 := (131109024813/250000000000000000)
  k0 := (855904011056519/250000000000000000)
  k6 := (441697376948899/40000000000000000)
  q := (175368184115591503151/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15377]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15377]

theorem width_15378 : mW 15378 = 450971916717083 := by
  have hu : mW 15378 ≤ 450971916717083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15378 ≤ 450971916717082 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15378 : RowArithmetic 15378 (43469012928224689847/40000000000000000000000) (1859512504544004619439/3125000000000000000000) (28653645144477/5000000000000000000000) where
  r0 := (16387029549/31250000000000000)
  k0 := (3423449069789823/1000000000000000000)
  k6 := (11042075384382303/1000000000000000000)
  q := (35074777262300611793/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15378]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15378]

theorem width_15379 : mW 15379 = 451074565306820 := by
  have hu : mW 15379 ≤ 451074565306820 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15379 ≤ 451074565306819 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15379 : RowArithmetic 15379 (135837794640889861939/125000000000000000000000) (595034558752075225805933/1000000000000000000000000) (2864880930197373/500000000000000000000000) where
  r0 := (524333800199/1000000000000000000)
  k0 := (1711641057176391/500000000000000000)
  k6 := (11041716380061819/1000000000000000000)
  q := (175379588322016539053/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15379]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15379]

theorem width_15380 : mW 15380 = 451177230584401 := by
  have hu : mW 15380 ≤ 451177230584401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15380 ≤ 451177230584400 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15380 : RowArithmetic 15380 (135834924504380693279/125000000000000000000000) (148756279313865232244951/250000000000000000000000) (5728794920085131/1000000000000000000000000) where
  r0 := (524282663143/1000000000000000000)
  k0 := (855778794477801/250000000000000000)
  k6 := (11041357410755329/1000000000000000000)
  q := (175385290147150026033/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15380]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15380]

theorem width_15381 : mW 15381 = 451279912551452 := by
  have hu : mW 15381 ≤ 451279912551452 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15381 ≤ 451279912551451 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15381 : RowArithmetic 15381 (217331287985596033011/200000000000000000000000) (297507838481996322310441/500000000000000000000000) (5727828207897447/1000000000000000000000000) where
  r0 := (524231534399/1000000000000000000)
  k0 := (3422948260464603/1000000000000000000)
  k6 := (5520499238228571/500000000000000000)
  q := (35078198357384319917/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15381]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15381]

theorem width_15382 : mW 15382 = 451382611209601 := by
  have hu : mW 15382 ≤ 451382611209601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15382 ≤ 451382611209600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15382 : RowArithmetic 15382 (135829186100563194609/125000000000000000000000) (595006237877424503419907/1000000000000000000000000) (1431715430940647/250000000000000000000000) where
  r0 := (104836082793/200000000000000000)
  k0 := (3422781362009229/1000000000000000000)
  k6 := (11040639577161569/1000000000000000000)
  q := (175396693241349336449/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15382]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15382]

theorem width_15383 : mW 15383 = 451485326560477 := by
  have hu : mW 15383 ≤ 451485326560477 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15383 ≤ 451485326560476 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15383 : RowArithmetic 15383 (1086610542663204704021/1000000000000000000000000) (37187299999719416417417/62500000000000000000000) (5725895467611461/1000000000000000000000000) where
  r0 := (262064650919/500000000000000000)
  k0 := (684522896507613/200000000000000000)
  k6 := (276007017821573/25000000000000000)
  q := (17540239451045131043/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15383]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15383]

theorem width_15384 : mW 15384 = 451588058605706 := by
  have hu : mW 15384 ≤ 451588058605706 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15384 ≤ 451588058605705 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15384 : RowArithmetic 15384 (543293800751331059563/500000000000000000000000) (74373420414750671393671/125000000000000000000000) (5724929439375037/1000000000000000000000000) where
  r0 := (524078198017/1000000000000000000)
  k0 := (3422447622050621/1000000000000000000)
  k6 := (11039921883555509/1000000000000000000)
  q := (175408095594245592391/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15384]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15384]

theorem width_15385 : mW 15385 = 451690807346916 := by
  have hu : mW 15385 ≤ 451690807346916 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15385 ≤ 451690807346915 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15385 : RowArithmetic 15385 (543282332660731076511/500000000000000000000000) (594977927844662927774169/1000000000000000000000000) (5723963638984287/1000000000000000000000000) where
  r0 := (524027102501/1000000000000000000)
  k0 := (3422280780546411/1000000000000000000)
  k6 := (11039563089233649/1000000000000000000)
  q := (21926724561593781283/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15385]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15385]

theorem width_15386 : mW 15386 = 451793572785737 := by
  have hu : mW 15386 ≤ 451793572785737 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15386 ≤ 451793572785736 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15386 : RowArithmetic 15386 (543270867059094497897/500000000000000000000000) (118993698715047553427627/200000000000000000000000) (2861499033185093/500000000000000000000000) where
  r0 := (261988007643/500000000000000000)
  k0 := (855528489503787/250000000000000000)
  k6 := (2207840865978331/200000000000000000)
  q := (175419497205983349039/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15386]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15386]

theorem width_15387 : mW 15387 = 451896354923795 := by
  have hu : mW 15387 ≤ 451896354923795 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15387 ≤ 451896354923794 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15387 : RowArithmetic 15387 (1086518807891428704173/1000000000000000000000000) (74369882563685535510419/125000000000000000000000) (5722032721463781/1000000000000000000000000) where
  r0 := (130981234093/250000000000000000)
  k0 := (3421947154459607/1000000000000000000)
  k6 := (2207769121104769/200000000000000000)
  q := (175425197733962950777/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15387]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15387]

theorem width_15388 : mW 15388 = 451999153762718 := by
  have hu : mW 15388 ≤ 451999153762718 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15388 ≤ 451999153762717 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15388 : RowArithmetic 15388 (543247943319883586571/500000000000000000000000) (118989925729431402705577/200000000000000000000000) (45768540833569/8000000000000000000000) where
  r0 := (130968466439/250000000000000000)
  k0 := (1710890184936383/500000000000000000)
  k6 := (1379810864515567/125000000000000000)
  q := (175430898076707114599/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15388]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15388]

theorem width_15389 : mW 15389 = 452101969304136 := by
  have hu : mW 15389 ≤ 452101969304136 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15389 ≤ 452101969304135 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15389 : RowArithmetic 15389 (43458918814471605479/40000000000000000000000) (74367524748501322167719/125000000000000000000000) (1430025678624567/250000000000000000000000) where
  r0 := (523822803437/1000000000000000000)
  k0 := (855403401063533/250000000000000000)
  k6 := (11038128261688047/1000000000000000000)
  q := (21929574779279237087/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15389]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15389]

theorem width_15390 : mW 15390 = 452204801549675 := by
  have hu : mW 15390 ≤ 452204801549675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15390 ≤ 452204801549674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15390 : RowArithmetic 15390 (1086450059056085194333/1000000000000000000000000) (594930768531799591603019/1000000000000000000000000) (5719138052301339/1000000000000000000000000) where
  r0 := (130942937353/250000000000000000)
  k0 := (3421446857596681/1000000000000000000)
  k6 := (11037769642208699/1000000000000000000)
  q := (43860574551640337581/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15390]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15390]

theorem width_15391 : mW 15391 = 452307650500965 := by
  have hu : mW 15391 ≤ 452307650500965 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15391 ≤ 452307650500964 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15391 : RowArithmetic 15391 (543213576360619553869/500000000000000000000000) (297460670139139417937553/500000000000000000000000) (142954340438411/25000000000000000000000) where
  r0 := (1636627199/3125000000000000)
  k0 := (3421280129899919/1000000000000000000)
  k6 := (11037411057680813/1000000000000000000)
  q := (35089599598741505161/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15391]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15391]

theorem width_15392 : mW 15392 = 452410516159633 := by
  have hu : mW 15392 ≤ 452410516159633 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15392 ≤ 452410516159632 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15392 : RowArithmetic 15392 (1086404251355840165507/1000000000000000000000000) (18590997288350094577991/31250000000000000000000) (5717209410134741/1000000000000000000000000) where
  r0 := (523669666239/1000000000000000000)
  k0 := (855278355290021/250000000000000000)
  k6 := (1379631563512339/125000000000000000)
  q := (175453697595690470533/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15392]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15392]

theorem width_15393 : mW 15393 = 452513398527308 := by
  have hu : mW 15393 ≤ 452513398527308 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15393 ≤ 452513398527307 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15393 : RowArithmetic 15393 (1086381354958476494791/1000000000000000000000000) (297451243689163553315303/500000000000000000000000) (5716245430027409/1000000000000000000000000) where
  r0 := (261809318543/500000000000000000)
  k0 := (3420946731370149/1000000000000000000)
  k6 := (5518346996728361/500000000000000000)
  q := (175459397012528228967/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15393]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15393]

theorem width_15394 : mW 15394 = 452616297605618 := by
  have hu : mW 15394 ≤ 452616297605618 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15394 ≤ 452616297605617 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15394 : RowArithmetic 15394 (271589615881934268277/250000000000000000000000) (297446531365702967042757/500000000000000000000000) (1428820419286413/250000000000000000000000) where
  r0 := (523567616221/1000000000000000000)
  k0 := (3420780060532883/1000000000000000000)
  k6 := (5518167756874583/500000000000000000)
  q := (175465096244238842637/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15394]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15394]

theorem width_15395 : mW 15395 = 452719213396192 := by
  have hu : mW 15395 ≤ 452719213396192 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15395 ≤ 452719213396191 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15395 : RowArithmetic 15395 (1086335577062211054053/1000000000000000000000000) (297441819643097286426557/500000000000000000000000) (571431815142069/100000000000000000000000) where
  r0 := (523516603641/1000000000000000000)
  k0 := (427576676080157/125000000000000000)
  k6 := (11035977068970373/1000000000000000000)
  q := (2741731176419380471/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15395]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15395]

theorem width_15396 : mW 15396 = 452822145900657 := by
  have hu : mW 15396 ≤ 452822145900657 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15396 ≤ 452822145900656 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15396 : RowArithmetic 15396 (543156347780244388717/500000000000000000000000) (594874217042448082568291/1000000000000000000000000) (1428338713195949/250000000000000000000000) where
  r0 := (32716599959/62500000000000000)
  k0 := (213777923480719/62500000000000000)
  k6 := (11035618659114669/1000000000000000000)
  q := (175476494152350787157/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15396]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15396]

theorem width_15397 : mW 15397 = 452925095120644 := by
  have hu : mW 15397 ≤ 452925095120644 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15397 ≤ 452925095120643 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15397 : RowArithmetic 15397 (13578622737764496863/12500000000000000000000) (594864795999921587619971/1000000000000000000000000) (5712391781166217/1000000000000000000000000) where
  r0 := (523414603329/1000000000000000000)
  k0 := (1710140080841563/500000000000000000)
  k6 := (5517630142088193/500000000000000000)
  q := (8774109641439409321/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15397]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15397]

theorem width_15398 : mW 15398 = 453028061057779 := by
  have hu : mW 15398 ≤ 453028061057779 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15398 ≤ 453028061057778 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15398 : RowArithmetic 15398 (1086266947442815669873/1000000000000000000000000) (297427688079185154090791/500000000000000000000000) (5711428936499291/1000000000000000000000000) where
  r0 := (523363615593/1000000000000000000)
  k0 := (342011356660909/100000000000000000)
  k6 := (5517450972074927/500000000000000000)
  q := (87743945660085288873/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15398]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15398]

theorem width_15399 : mW 15399 = 453131043713692 := by
  have hu : mW 15399 ≤ 453131043713692 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15399 ≤ 453131043713691 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15399 : RowArithmetic 15399 (271561020206011851737/250000000000000000000000) (594845957517549511512689/1000000000000000000000000) (713808289839291/125000000000000000000000) where
  r0 := (104662527227/200000000000000000)
  k0 := (683989398093779/200000000000000000)
  k6 := (2758635909757351/250000000000000000)
  q := (87746794813257994011/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15399]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15399]

theorem width_15400 : mW 15400 = 453234043090012 := by
  have hu : mW 15400 ≤ 453234043090012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15400 ≤ 453234043090011 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15400 : RowArithmetic 15400 (1086221219163446675947/1000000000000000000000000) (594836540077214492815201/1000000000000000000000000) (2854751963871341/500000000000000000000000) where
  r0 := (65407708119/125000000000000000)
  k0 := (213736277078469/62500000000000000)
  k6 := (1103418536880937/100000000000000000)
  q := (175499287747842441209/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15400]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15400]

theorem width_15401 : mW 15401 = 453337059188367 := by
  have hu : mW 15401 ≤ 453337059188367 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15401 ≤ 453337059188366 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15401 : RowArithmetic 15401 (1086198362459606040343/1000000000000000000000000) (148706780959280192438171/250000000000000000000000) (285427088175787/50000000000000000000000) where
  r0 := (523210702043/1000000000000000000)
  k0 := (683922778993683/200000000000000000)
  k6 := (5516913566742043/500000000000000000)
  q := (175504985684167958341/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15401]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15401]

theorem width_15402 : mW 15402 = 453440092010386 := by
  have hu : mW 15402 ≤ 453440092010386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15402 ≤ 453440092010385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15402 : RowArithmetic 15402 (1086175510711118238891/1000000000000000000000000) (594817708797023733148507/1000000000000000000000000) (2853789912982453/500000000000000000000000) where
  r0 := (523159747407/1000000000000000000)
  k0 := (27355579004857/8000000000000000)
  k6 := (11033468933047889/1000000000000000000)
  q := (175510683435510557527/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15402]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15402]

theorem width_15403 : mW 15403 = 453543141557698 := by
  have hu : mW 15403 ≤ 453543141557698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15403 ≤ 453543141557697 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15403 : RowArithmetic 15403 (271538165979144130429/250000000000000000000000) (11896165899133579984851/20000000000000000000000) (570661811502161/100000000000000000000000) where
  r0 := (6538860013/12500000000000000)
  k0 := (1709640437580663/500000000000000000)
  k6 := (2758277691873779/250000000000000000)
  q := (85701357911078249/488281250000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15403]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15403]

theorem width_15404 : mW 15404 = 453646207831932 := by
  have hu : mW 15404 ≤ 453646207831932 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15404 ≤ 453646207831931 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15404 : RowArithmetic 15404 (543064911037287325033/500000000000000000000000) (594798882315842126705679/1000000000000000000000000) (2852828315308653/500000000000000000000000) where
  r0 := (261528931471/500000000000000000)
  k0 := (1709557196816891/500000000000000000)
  k6 := (2206550527364021/200000000000000000)
  q := (175522078383319059877/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15404]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15404]

theorem width_15405 : mW 15405 = 453749290834716 := by
  have hu : mW 15405 ≤ 453749290834716 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15405 ≤ 453749290834715 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15405 : RowArithmetic 15405 (217221397036741446303/200000000000000000000000) (594789470874268847965763/1000000000000000000000000) (178271730396359/31250000000000000000000) where
  r0 := (52300693311/100000000000000000)
  k0 := (68378958620349/20000000000000000)
  k6 := (2758098635254299/250000000000000000)
  q := (175527775579820984639/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15405]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15405]

theorem width_15406 : mW 15406 = 453852390567680 := by
  have hu : mW 15406 ≤ 453852390567680 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15406 ≤ 453852390567679 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15406 : RowArithmetic 15406 (271521038310642178289/250000000000000000000000) (594780060631714905683577/1000000000000000000000000) (114074686823033/20000000000000000000000) where
  r0 := (261478005771/500000000000000000)
  k0 := (854695371827139/250000000000000000)
  k6 := (1103203648008073/100000000000000000)
  q := (175533472591412034653/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15406]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15406]

theorem width_15407 : mW 15407 = 453955507032453 := by
  have hu : mW 15407 ≤ 453955507032453 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15407 ≤ 453955507032452 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15407 : RowArithmetic 15407 (54303066312487719409/50000000000000000000000) (594770651587936083601811/1000000000000000000000000) (2851386767976663/500000000000000000000000) where
  r0 := (522905098237/1000000000000000000)
  k0 := (3418615062506593/1000000000000000000)
  k6 := (11031678454005049/1000000000000000000)
  q := (43884792354527553353/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15407]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15407]

theorem width_15408 : mW 15408 = 454058640230664 := by
  have hu : mW 15408 ≤ 454058640230664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15408 ≤ 454058640230663 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15408 : RowArithmetic 15408 (135754813025482507493/125000000000000000000000) (594761243742688358476403/1000000000000000000000000) (5701812957020073/1000000000000000000000000) where
  r0 := (522854193193/1000000000000000000)
  k0 := (3418448656607783/1000000000000000000)
  k6 := (5515660231392249/500000000000000000)
  q := (175544866059933521487/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15408]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15408]

theorem width_15409 : mW 15409 = 454161790163942 := by
  have hu : mW 15409 ≤ 454161790163942 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15409 ≤ 454161790163941 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15409 : RowArithmetic 15409 (543007843551741020867/500000000000000000000000) (594751837095727590411547/1000000000000000000000000) (5700852604283477/1000000000000000000000000) where
  r0 := (65350412051/125000000000000000)
  k0 := (3418282269608349/1000000000000000000)
  k6 := (551548125320671/50000000000000000)
  q := (175550562516899956529/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15409]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15409]

theorem width_15410 : mW 15410 = 454264956833917 := by
  have hu : mW 15410 ≤ 454264956833917 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15410 ≤ 454264956833916 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15410 : RowArithmetic 15410 (1085992874947216821719/1000000000000000000000000) (594742431646809869296827/1000000000000000000000000) (5699892477675137/1000000000000000000000000) where
  r0 := (13068810197/25000000000000000)
  k0 := (3338003810063/976562500000000)
  k6 := (5515302292443081/500000000000000000)
  q := (17555625878902751327/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15410]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15410]

theorem width_15411 : mW 15411 = 454368140242217 := by
  have hu : mW 15411 ≤ 454368140242217 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15411 ≤ 454368140242216 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15411 : RowArithmetic 15411 (542985033866831033691/500000000000000000000000) (594733027395691309901107/1000000000000000000000000) (5698932577126701/1000000000000000000000000) where
  r0 := (261350763803/500000000000000000)
  k0 := (427243694036153/125000000000000000)
  k6 := (689390418637317/62500000000000000)
  q := (87780977438167091761/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15411]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15411]

theorem width_15412 : mW 15412 = 454471340390471 := by
  have hu : mW 15412 ≤ 454471340390471 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15412 ≤ 454471340390470 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15412 : RowArithmetic 15412 (1085947265461415620357/1000000000000000000000000) (297361812171063994993247/500000000000000000000000) (5697972902569831/1000000000000000000000000) where
  r0 := (261325327793/500000000000000000)
  k0 := (3417783221965241/1000000000000000000)
  k6 := (11029888846340499/1000000000000000000)
  q := (175567650778837956177/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15412]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15412]

theorem width_15413 : mW 15413 = 454574557280311 := by
  have hu : mW 15413 ≤ 454574557280311 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15413 ≤ 454574557280310 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15413 : RowArithmetic 15413 (108592446812907482797/100000000000000000000000) (148678555621469057199471/250000000000000000000000) (5697013453936179/1000000000000000000000000) where
  r0 := (261299895909/500000000000000000)
  k0 := (3417616910528783/1000000000000000000)
  k6 := (11029531029310791/1000000000000000000)
  q := (175573346496556817211/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15413]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15413]

theorem width_15414 : mW 15414 = 454677790913363 := by
  have hu : mW 15414 ≤ 454677790913363 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15414 ≤ 454677790913362 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15414 : RowArithmetic 15414 (271475418933809888399/250000000000000000000000) (951527714922707667823/1600000000000000000000) (712006778894687/125000000000000000000000) where
  r0 := (261274468149/500000000000000000)
  k0 := (3417450617969527/1000000000000000000)
  k6 := (5514586623551151/500000000000000000)
  q := (175579042029508749681/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15414]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15414]

theorem width_15415 : mW 15415 = 454781041291259 := by
  have hu : mW 15415 ≤ 454781041291259 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15415 ≤ 454781041291258 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15415 : RowArithmetic 15415 (217175777655701632509/200000000000000000000000) (594695422364332529074331/1000000000000000000000000) (2847547617082743/500000000000000000000000) where
  r0 := (522498089027/1000000000000000000)
  k0 := (6834568688587/2000000000000000)
  k6 := (11028815499709383/1000000000000000000)
  q := (17558473737771173373/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15415]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15415]

theorem width_15416 : mW 15416 = 454884308415628 := by
  have hu : mW 15416 ≤ 454884308415628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15416 ≤ 454884308415627 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15416 : RowArithmetic 15416 (1085856105757480532039/1000000000000000000000000) (148671506024638358227317/250000000000000000000000) (5694136462891913/1000000000000000000000000) where
  r0 := (522447250001/1000000000000000000)
  k0 := (27336944715923/8000000000000000)
  k6 := (2757114446781597/250000000000000000)
  q := (87795216270591873291/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15416]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15416]

theorem width_15417 : mW 15417 = 454987592288099 := by
  have hu : mW 15417 ≤ 454987592288099 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15417 ≤ 454987592288098 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15417 : RowArithmetic 15417 (1085833328170757047317/1000000000000000000000000) (148669156757277852692599/250000000000000000000000) (569317791726857/100000000000000000000000) where
  r0 := (522396419219/1000000000000000000)
  k0 := (3416951853559639/1000000000000000000)
  k6 := (1378512513668459/125000000000000000)
  q := (175596127519942762547/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15417]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15417]

theorem width_15418 : mW 15418 = 455090892910302 := by
  have hu : mW 15418 ≤ 455090892910302 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15418 ≤ 455090892910301 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15418 : RowArithmetic 15418 (1085810555516938267599/1000000000000000000000000) (594667231155763156656393/1000000000000000000000000) (2846109798613631/500000000000000000000000) where
  r0 := (522345596679/1000000000000000000)
  k0 := (106774551140547/31250000000000000)
  k6 := (1378467808295949/125000000000000000)
  q := (175601822314006753021/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15418]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15418]

theorem width_15419 : mW 15419 = 455194210283867 := by
  have hu : mW 15419 ≤ 455194210283867 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15419 ≤ 455194210283866 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15419 : RowArithmetic 15419 (21715755755892505203/20000000000000000000000) (5946578364782652641459/10000000000000000000000) (5691261502699819/1000000000000000000000000) where
  r0 := (522294782379/1000000000000000000)
  k0 := (1708309719150091/500000000000000000)
  k6 := (5513692429090253/500000000000000000)
  q := (35121503384678737297/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15419]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15419]

theorem width_15420 : mW 15420 = 455297544410423 := by
  have hu : mW 15420 ≤ 455297544410423 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15420 ≤ 455297544410422 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15420 : RowArithmetic 15420 (67860314062651245849/62500000000000000000000) (594648442996374397317077/1000000000000000000000000) (88910994275283/15625000000000000000000) where
  r0 := (522243976317/1000000000000000000)
  k0 := (683290651792777/200000000000000000)
  k6 := (11027027284780773/1000000000000000000)
  q := (43903302837030382127/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15420]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15420]

theorem width_15421 : mW 15421 = 455400895291601 := by
  have hu : mW 15421 ≤ 455400895291601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15421 ≤ 455400895291600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15421 : RowArithmetic 15421 (1085742267138924036741/1000000000000000000000000) (148659762677461844416913/250000000000000000000000) (5689345989914009/1000000000000000000000000) where
  r0 := (130548294623/250000000000000000)
  k0 := (1708143549244047/500000000000000000)
  k6 := (172291714783793/15625000000000000)
  q := (10976181599263015109/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15421]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15421]

theorem width_15422 : mW 15422 = 455504262929029 := by
  have hu : mW 15422 ≤ 455504262929029 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15422 ≤ 455504262929028 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15422 : RowArithmetic 15422 (1085719514202740826173/1000000000000000000000000) (594629659618441024927491/1000000000000000000000000) (1137677714303889/200000000000000000000000) where
  r0 := (522142388901/1000000000000000000)
  k0 := (854030239216437/250000000000000000)
  k6 := (5513156121160403/500000000000000000)
  q := (87812299821835892969/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15422]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15422]

theorem width_15423 : mW 15423 = 455607647324338 := by
  have hu : mW 15423 ≤ 455607647324338 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15423 ≤ 455607647324337 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15423 : RowArithmetic 15423 (542848383096236532507/500000000000000000000000) (118924053944382456479623/200000000000000000000000) (5687431378366341/1000000000000000000000000) where
  r0 := (522091607543/1000000000000000000)
  k0 := (136638193363853/40000000000000000)
  k6 := (5512977386624649/500000000000000000)
  q := (175630293514530117921/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15423]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15423]

theorem width_15424 : mW 15424 = 455711048479159 := by
  have hu : mW 15424 ≤ 455711048479159 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15424 ≤ 455711048479158 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15424 : RowArithmetic 15424 (271418505776681005939/250000000000000000000000) (118922176204003623627931/200000000000000000000000) (1137294882077329/200000000000000000000000) where
  r0 := (104408166883/200000000000000000)
  k0 := (3415788730172763/1000000000000000000)
  k6 := (11025597338942591/1000000000000000000)
  q := (87817993600400595807/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15424]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15424]

theorem width_15425 : mW 15425 = 455814466395120 := by
  have hu : mW 15425 ≤ 455814466395120 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15425 ≤ 455814466395119 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15425 : RowArithmetic 15425 (542825642472049239377/500000000000000000000000) (594601493512515585361933/1000000000000000000000000) (2842758833756183/500000000000000000000000) where
  r0 := (521990069517/1000000000000000000)
  k0 := (3415622645097809/1000000000000000000)
  k6 := (11025239939395051/1000000000000000000)
  q := (17564168070250295803/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15425]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15425]

theorem width_15426 : mW 15426 = 455917901073852 := by
  have hu : mW 15426 ≤ 455917901073852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15426 ≤ 455917901073851 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15426 : RowArithmetic 15426 (1085628551703200713369/1000000000000000000000000) (594592107199161795973837/1000000000000000000000000) (355285071854719/62500000000000000000000) where
  r0 := (104387862569/200000000000000000)
  k0 := (3415456578861127/1000000000000000000)
  k6 := (2756220643650261/250000000000000000)
  q := (17564737401965336527/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15426]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15426]

theorem width_15427 : mW 15427 = 456021352516986 := by
  have hu : mW 15427 ≤ 456021352516986 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15427 ≤ 456021352516985 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15427 : RowArithmetic 15427 (542802911691317758801/500000000000000000000000) (594582722079713926396713/1000000000000000000000000) (5683604856808083/1000000000000000000000000) where
  r0 := (521888564399/1000000000000000000)
  k0 := (426911316433183/125000000000000000)
  k6 := (11024525244554939/1000000000000000000)
  q := (175653067152270358527/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15427]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15427]

theorem width_15428 : mW 15428 = 456124820726150 := by
  have hu : mW 15428 ≤ 456124820726150 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15428 ≤ 456124820726149 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15428 : RowArithmetic 15428 (1085583099981009185477/1000000000000000000000000) (14864333453848231028233/25000000000000000000000) (355165549302637/62500000000000000000000) where
  r0 := (32614864011/62500000000000000)
  k0 := (3415124502903753/1000000000000000000)
  k6 := (2204833589850221/200000000000000000)
  q := (21957345012546485011/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15428]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15428]

theorem width_15429 : mW 15429 = 456228305702976 := by
  have hu : mW 15429 ≤ 456228305702976 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15429 ≤ 456228305702975 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15429 : RowArithmetic 15429 (542780190748463593013/500000000000000000000000) (23782558216862601827213/40000000000000000000000) (5681692945709893/1000000000000000000000000) where
  r0 := (260893546087/500000000000000000)
  k0 := (1707479246586097/500000000000000000)
  k6 := (11023810688683913/1000000000000000000)
  q := (175664452863975869329/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15429]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15429]

theorem width_15430 : mW 15430 = 456331807449094 := by
  have hu : mW 15430 ≤ 456331807449094 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15430 ≤ 456331807449093 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15430 : RowArithmetic 15430 (135692208491124519911/125000000000000000000000) (37159660867648671585333/62500000000000000000000) (5680737327343301/1000000000000000000000000) where
  r0 := (65217046049/125000000000000000)
  k0 := (3414792502270263/1000000000000000000)
  k6 := (11023453462847733/1000000000000000000)
  q := (87835072721550131361/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15430]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15430]

theorem width_15431 : mW 15431 = 456435325966134 := by
  have hu : mW 15431 ≤ 456435325966134 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15431 ≤ 456435325966133 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15431 : RowArithmetic 15431 (1085514959275823250497/1000000000000000000000000) (37159074596007984718809/62500000000000000000000) (1419945483418639/250000000000000000000000) where
  r0 := (130421413207/250000000000000000)
  k0 := (3414626530194159/1000000000000000000)
  k6 := (551154813586847/50000000000000000)
  q := (175675837837762993833/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15431]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15431]

theorem width_15432 : mW 15432 = 456538861255727 := by
  have hu : mW 15432 ≤ 456538861255727 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15432 ≤ 456538861255726 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15432 : RowArithmetic 15432 (1085492255536015777801/1000000000000000000000000) (594535814382569712078429/1000000000000000000000000) (567882676463581/100000000000000000000000) where
  r0 := (521634945479/1000000000000000000)
  k0 := (341446057693681/100000000000000000)
  k6 := (2755684778836477/250000000000000000)
  q := (4392038251199549833/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15432]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15432]

theorem width_15433 : mW 15433 = 456642413319503 := by
  have hu : mW 15433 ≤ 456642413319503 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15433 ≤ 456642413319502 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15433 : RowArithmetic 15433 (542734778354090948241/500000000000000000000000) (297263218210731023717827/500000000000000000000000) (709733977519907/125000000000000000000000) where
  r0 := (104316849269/200000000000000000)
  k0 := (3414294642500959/1000000000000000000)
  k6 := (11022381993669011/1000000000000000000)
  q := (8784361103688759447/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15433]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15433]

theorem width_15434 : mW 15434 = 456745982159092 := by
  have hu : mW 15434 ≤ 456745982159092 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15434 ≤ 456745982159091 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15434 : RowArithmetic 15434 (542723431395465133151/500000000000000000000000) (297258529826281277242131/500000000000000000000000) (5676917100177109/1000000000000000000000000) where
  r0 := (260766777711/500000000000000000)
  k0 := (3414128726876259/1000000000000000000)
  k6 := (11022024906700629/1000000000000000000)
  q := (175692913915160505543/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15434]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15434]

theorem width_15435 : mW 15435 = 456849567776124 := by
  have hu : mW 15435 ≤ 456849567776124 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15435 ≤ 456849567776123 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15435 : RowArithmetic 15435 (271356043445717512817/250000000000000000000000) (594507684075628869636151/1000000000000000000000000) (1418990651155403/250000000000000000000000) where
  r0 := (52148287271/100000000000000000)
  k0 := (3413962830065451/1000000000000000000)
  k6 := (11021667854435137/1000000000000000000)
  q := (43924651393038966269/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15435]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15435]

theorem width_15436 : mW 15436 = 456953170172232 := by
  have hu : mW 15436 ≤ 456953170172232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15436 ≤ 456953170172231 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15436 : RowArithmetic 15436 (542700744841304962393/500000000000000000000000) (118899661938083760555323/200000000000000000000000) (1418752083356249/250000000000000000000000) where
  r0 := (260716099103/500000000000000000)
  k0 := (1706898476030729/500000000000000000)
  k6 := (2755327709216729/250000000000000000)
  q := (35140859408955837317/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15436]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15436]

theorem width_15437 : mW 15437 = 457056789349045 := by
  have hu : mW 15437 ≤ 457056789349045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15437 ≤ 457056789349044 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15437 : RowArithmetic 15437 (1085378810488760391183/1000000000000000000000000) (118897787299338055368101/200000000000000000000000) (354628392907473/62500000000000000000000) where
  r0 := (521381531909/1000000000000000000)
  k0 := (3413631092863749/1000000000000000000)
  k6 := (11020953853990347/1000000000000000000)
  q := (175709988333048386211/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15437]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15437]

theorem width_15438 : mW 15438 = 457160425308193 := by
  have hu : mW 15438 ≤ 457160425308193 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15438 ≤ 457160425308192 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15438 : RowArithmetic 15438 (217071227239986425307/200000000000000000000000) (118895912898840230496431/200000000000000000000000) (2836550231918823/500000000000000000000000) where
  r0 := (65166359227/125000000000000000)
  k0 := (3413465252465243/1000000000000000000)
  k6 := (2755149226449953/250000000000000000)
  q := (175715679436981377197/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15438]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15438]

theorem width_15439 : mW 15439 = 457264078051309 := by
  have hu : mW 15439 ≤ 457264078051309 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15439 ≤ 457264078051308 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15439 : RowArithmetic 15439 (108533346681473531673/100000000000000000000000) (148617548420677364493797/250000000000000000000000) (2836073432655769/500000000000000000000000) where
  r0 := (521280223927/1000000000000000000)
  k0 := (85332485771717/25000000000000000)
  k6 := (11020239992289693/1000000000000000000)
  q := (175721370356596069883/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15439]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15439]

theorem width_15440 : mW 15440 = 457367747580021 := by
  have hu : mW 15440 ≤ 457367747580021 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15440 ≤ 457367747580020 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15440 : RowArithmetic 15440 (1085310802331782307411/1000000000000000000000000) (297230412030986629721083/500000000000000000000000) (141779837271841/25000000000000000000000) where
  r0 := (260614791119/500000000000000000)
  k0 := (426641703507963/125000000000000000)
  k6 := (1377485389181797/125000000000000000)
  q := (175727061091910371709/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15440]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15440]

theorem width_15441 : mW 15441 = 457471433895962 := by
  have hu : mW 15441 ≤ 457471433895962 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15441 ≤ 457471433895961 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15441 : RowArithmetic 15441 (1085288142749684291483/1000000000000000000000000) (118890291126350130112731/200000000000000000000000) (5670240340456309/1000000000000000000000000) where
  r0 := (130294737187/250000000000000000)
  k0 := (170648392202489/50000000000000000)
  k6 := (5509763134644123/500000000000000000)
  q := (10983296977683886701/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15441]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15441]

theorem width_15442 : mW 15442 = 457575137000763 := by
  have hu : mW 15442 ≤ 457575137000763 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15442 ≤ 457575137000762 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15442 : RowArithmetic 15442 (1695727325104771293/1562500000000000000000) (594442088391799869049217/1000000000000000000000000) (1417321853497989/250000000000000000000000) where
  r0 := (4071315027/7812500000000000)
  k0 := (853200519706593/250000000000000000)
  k6 := (1101916945978569/100000000000000000)
  q := (35147688401941883609/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15442]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15442]

theorem width_15443 : mW 15443 = 457678856896053 := by
  have hu : mW 15443 ≤ 457678856896053 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15443 ≤ 457678856896052 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15443 : RowArithmetic 15443 (1085242838282503838279/1000000000000000000000000) (148608180585469803132031/250000000000000000000000) (70854183892663/12500000000000000000000) where
  r0 := (521077706359/1000000000000000000)
  k0 := (3412636332386393/1000000000000000000)
  k6 := (11018812684941097/1000000000000000000)
  q := (87872066096114981471/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15443]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15443]

theorem width_15444 : mW 15444 = 457782593583465 := by
  have hu : mW 15444 ≤ 457782593583465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15444 ≤ 457782593583464 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15444 : RowArithmetic 15444 (542610096697323812993/500000000000000000000000) (594423357481746945771029/1000000000000000000000000) (5667382232651997/1000000000000000000000000) where
  r0 := (104205419491/200000000000000000)
  k0 := (213279412795377/62500000000000000)
  k6 := (11018455944748857/1000000000000000000)
  q := (175749822190521717751/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15444]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15444]

theorem width_15445 : mW 15445 = 457886347064629 := by
  have hu : mW 15445 ≤ 457886347064629 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15445 ≤ 457886347064628 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15445 : RowArithmetic 15445 (1085197553402099187491/1000000000000000000000000) (148603498452790377848939/250000000000000000000000) (1416607494410331/250000000000000000000000) where
  r0 := (520976496743/1000000000000000000)
  k0 := (13649219583379/4000000000000000)
  k6 := (11018099239203359/1000000000000000000)
  q := (2746179875071915241/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15445]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15445]

theorem width_15446 : mW 15446 = 457990117341176 := by
  have hu : mW 15446 ≤ 457990117341176 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15446 ≤ 457990117341175 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15446 : RowArithmetic 15446 (1085174918303472891009/1000000000000000000000000) (118880926265976271488783/200000000000000000000000) (5665477946313533/1000000000000000000000000) where
  r0 := (520925904221/1000000000000000000)
  k0 := (3412139205738733/1000000000000000000)
  k6 := (5508871284149499/500000000000000000)
  q := (43940300408622606503/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15446]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15446]

theorem width_15447 : mW 15447 = 458093904414738 := by
  have hu : mW 15447 ≤ 458093904414738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15447 ≤ 458093904414737 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15447 : RowArithmetic 15447 (1085152288097383276503/1000000000000000000000000) (594395270037665065537829/1000000000000000000000000) (1416131534650287/250000000000000000000000) where
  r0 := (520875319887/1000000000000000000)
  k0 := (1705986767202083/500000000000000000)
  k6 := (2203477186406033/200000000000000000)
  q := (175766891080203156673/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15447]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15447]

theorem width_15448 : mW 15448 = 458197708286945 := by
  have hu : mW 15448 ≤ 458197708286945 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15448 ≤ 458197708286944 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15448 : RowArithmetic 15448 (271282415695611511549/250000000000000000000000) (594385909934271160868737/1000000000000000000000000) (707946819304593/125000000000000000000000) where
  r0 := (520824743739/1000000000000000000)
  k0 := (3411807881837231/1000000000000000000)
  k6 := (1377128666298907/125000000000000000)
  q := (21971572542719831459/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15448]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15448]

theorem width_15449 : mW 15449 = 458301528959430 := by
  have hu : mW 15449 ≤ 458301528959430 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15449 ≤ 458301528959429 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15449 : RowArithmetic 15449 (271276760589319103377/250000000000000000000000) (297188275509729180547349/500000000000000000000000) (1415655798438221/250000000000000000000000) where
  r0 := (20830967031/40000000000000000)
  k0 := (3411642248034113/1000000000000000000)
  k6 := (5508336381688333/500000000000000000)
  q := (21972283677396849047/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15449]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15449]

theorem width_15450 : mW 15450 = 458405366433823 := by
  have hu : mW 15450 ≤ 458405366433823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15450 ≤ 458405366433822 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15450 : RowArithmetic 15450 (271271106705122770861/250000000000000000000000) (594367193292985420265881/1000000000000000000000000) (1132334411296439/200000000000000000000000) where
  r0 := (520723615993/1000000000000000000)
  k0 := (213217289561937/62500000000000000)
  k6 := (5508158115490397/500000000000000000)
  q := (8789197915623472863/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15450]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15450]

theorem width_15451 : mW 15451 = 458509220711756 := by
  have hu : mW 15451 ≤ 458509220711756 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15451 ≤ 458509220711755 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15451 : RowArithmetic 15451 (271265454042676650537/250000000000000000000000) (594357836754611093372201/1000000000000000000000000) (5660721142557301/1000000000000000000000000) where
  r0 := (520673064393/1000000000000000000)
  k0 := (3411311036710601/1000000000000000000)
  k6 := (11015959733198037/1000000000000000000)
  q := (175789647021660521907/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15451]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15451]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15377 then ⟨(1086748294271959502673/1000000000000000000000000), (595053445361725785663493/1000000000000000000000000), (2865848212828139/500000000000000000000000)⟩ else
  if n = 15378 then ⟨(43469012928224689847/40000000000000000000000), (1859512504544004619439/3125000000000000000000), (28653645144477/5000000000000000000000)⟩ else
  if n = 15379 then ⟨(135837794640889861939/125000000000000000000000), (595034558752075225805933/1000000000000000000000000), (2864880930197373/500000000000000000000000)⟩ else
  if n = 15380 then ⟨(135834924504380693279/125000000000000000000000), (148756279313865232244951/250000000000000000000000), (5728794920085131/1000000000000000000000000)⟩ else
  if n = 15381 then ⟨(217331287985596033011/200000000000000000000000), (297507838481996322310441/500000000000000000000000), (5727828207897447/1000000000000000000000000)⟩ else
  if n = 15382 then ⟨(135829186100563194609/125000000000000000000000), (595006237877424503419907/1000000000000000000000000), (1431715430940647/250000000000000000000000)⟩ else
  if n = 15383 then ⟨(1086610542663204704021/1000000000000000000000000), (37187299999719416417417/62500000000000000000000), (5725895467611461/1000000000000000000000000)⟩ else
  if n = 15384 then ⟨(543293800751331059563/500000000000000000000000), (74373420414750671393671/125000000000000000000000), (5724929439375037/1000000000000000000000000)⟩ else
  if n = 15385 then ⟨(543282332660731076511/500000000000000000000000), (594977927844662927774169/1000000000000000000000000), (5723963638984287/1000000000000000000000000)⟩ else
  if n = 15386 then ⟨(543270867059094497897/500000000000000000000000), (118993698715047553427627/200000000000000000000000), (2861499033185093/500000000000000000000000)⟩ else
  if n = 15387 then ⟨(1086518807891428704173/1000000000000000000000000), (74369882563685535510419/125000000000000000000000), (5722032721463781/1000000000000000000000000)⟩ else
  if n = 15388 then ⟨(543247943319883586571/500000000000000000000000), (118989925729431402705577/200000000000000000000000), (45768540833569/8000000000000000000000)⟩ else
  if n = 15389 then ⟨(43458918814471605479/40000000000000000000000), (74367524748501322167719/125000000000000000000000), (1430025678624567/250000000000000000000000)⟩ else
  if n = 15390 then ⟨(1086450059056085194333/1000000000000000000000000), (594930768531799591603019/1000000000000000000000000), (5719138052301339/1000000000000000000000000)⟩ else
  if n = 15391 then ⟨(543213576360619553869/500000000000000000000000), (297460670139139417937553/500000000000000000000000), (142954340438411/25000000000000000000000)⟩ else
  if n = 15392 then ⟨(1086404251355840165507/1000000000000000000000000), (18590997288350094577991/31250000000000000000000), (5717209410134741/1000000000000000000000000)⟩ else
  if n = 15393 then ⟨(1086381354958476494791/1000000000000000000000000), (297451243689163553315303/500000000000000000000000), (5716245430027409/1000000000000000000000000)⟩ else
  if n = 15394 then ⟨(271589615881934268277/250000000000000000000000), (297446531365702967042757/500000000000000000000000), (1428820419286413/250000000000000000000000)⟩ else
  if n = 15395 then ⟨(1086335577062211054053/1000000000000000000000000), (297441819643097286426557/500000000000000000000000), (571431815142069/100000000000000000000000)⟩ else
  if n = 15396 then ⟨(543156347780244388717/500000000000000000000000), (594874217042448082568291/1000000000000000000000000), (1428338713195949/250000000000000000000000)⟩ else
  if n = 15397 then ⟨(13578622737764496863/12500000000000000000000), (594864795999921587619971/1000000000000000000000000), (5712391781166217/1000000000000000000000000)⟩ else
  if n = 15398 then ⟨(1086266947442815669873/1000000000000000000000000), (297427688079185154090791/500000000000000000000000), (5711428936499291/1000000000000000000000000)⟩ else
  if n = 15399 then ⟨(271561020206011851737/250000000000000000000000), (594845957517549511512689/1000000000000000000000000), (713808289839291/125000000000000000000000)⟩ else
  if n = 15400 then ⟨(1086221219163446675947/1000000000000000000000000), (594836540077214492815201/1000000000000000000000000), (2854751963871341/500000000000000000000000)⟩ else
  if n = 15401 then ⟨(1086198362459606040343/1000000000000000000000000), (148706780959280192438171/250000000000000000000000), (285427088175787/50000000000000000000000)⟩ else
  if n = 15402 then ⟨(1086175510711118238891/1000000000000000000000000), (594817708797023733148507/1000000000000000000000000), (2853789912982453/500000000000000000000000)⟩ else
  if n = 15403 then ⟨(271538165979144130429/250000000000000000000000), (11896165899133579984851/20000000000000000000000), (570661811502161/100000000000000000000000)⟩ else
  if n = 15404 then ⟨(543064911037287325033/500000000000000000000000), (594798882315842126705679/1000000000000000000000000), (2852828315308653/500000000000000000000000)⟩ else
  if n = 15405 then ⟨(217221397036741446303/200000000000000000000000), (594789470874268847965763/1000000000000000000000000), (178271730396359/31250000000000000000000)⟩ else
  if n = 15406 then ⟨(271521038310642178289/250000000000000000000000), (594780060631714905683577/1000000000000000000000000), (114074686823033/20000000000000000000000)⟩ else
  if n = 15407 then ⟨(54303066312487719409/50000000000000000000000), (594770651587936083601811/1000000000000000000000000), (2851386767976663/500000000000000000000000)⟩ else
  if n = 15408 then ⟨(135754813025482507493/125000000000000000000000), (594761243742688358476403/1000000000000000000000000), (5701812957020073/1000000000000000000000000)⟩ else
  if n = 15409 then ⟨(543007843551741020867/500000000000000000000000), (594751837095727590411547/1000000000000000000000000), (5700852604283477/1000000000000000000000000)⟩ else
  if n = 15410 then ⟨(1085992874947216821719/1000000000000000000000000), (594742431646809869296827/1000000000000000000000000), (5699892477675137/1000000000000000000000000)⟩ else
  if n = 15411 then ⟨(542985033866831033691/500000000000000000000000), (594733027395691309901107/1000000000000000000000000), (5698932577126701/1000000000000000000000000)⟩ else
  if n = 15412 then ⟨(1085947265461415620357/1000000000000000000000000), (297361812171063994993247/500000000000000000000000), (5697972902569831/1000000000000000000000000)⟩ else
  if n = 15413 then ⟨(108592446812907482797/100000000000000000000000), (148678555621469057199471/250000000000000000000000), (5697013453936179/1000000000000000000000000)⟩ else
  if n = 15414 then ⟨(271475418933809888399/250000000000000000000000), (951527714922707667823/1600000000000000000000), (712006778894687/125000000000000000000000)⟩ else
  if n = 15415 then ⟨(217175777655701632509/200000000000000000000000), (594695422364332529074331/1000000000000000000000000), (2847547617082743/500000000000000000000000)⟩ else
  if n = 15416 then ⟨(1085856105757480532039/1000000000000000000000000), (148671506024638358227317/250000000000000000000000), (5694136462891913/1000000000000000000000000)⟩ else
  if n = 15417 then ⟨(1085833328170757047317/1000000000000000000000000), (148669156757277852692599/250000000000000000000000), (569317791726857/100000000000000000000000)⟩ else
  if n = 15418 then ⟨(1085810555516938267599/1000000000000000000000000), (594667231155763156656393/1000000000000000000000000), (2846109798613631/500000000000000000000000)⟩ else
  if n = 15419 then ⟨(21715755755892505203/20000000000000000000000), (5946578364782652641459/10000000000000000000000), (5691261502699819/1000000000000000000000000)⟩ else
  if n = 15420 then ⟨(67860314062651245849/62500000000000000000000), (594648442996374397317077/1000000000000000000000000), (88910994275283/15625000000000000000000)⟩ else
  if n = 15421 then ⟨(1085742267138924036741/1000000000000000000000000), (148659762677461844416913/250000000000000000000000), (5689345989914009/1000000000000000000000000)⟩ else
  if n = 15422 then ⟨(1085719514202740826173/1000000000000000000000000), (594629659618441024927491/1000000000000000000000000), (1137677714303889/200000000000000000000000)⟩ else
  if n = 15423 then ⟨(542848383096236532507/500000000000000000000000), (118924053944382456479623/200000000000000000000000), (5687431378366341/1000000000000000000000000)⟩ else
  if n = 15424 then ⟨(271418505776681005939/250000000000000000000000), (118922176204003623627931/200000000000000000000000), (1137294882077329/200000000000000000000000)⟩ else
  if n = 15425 then ⟨(542825642472049239377/500000000000000000000000), (594601493512515585361933/1000000000000000000000000), (2842758833756183/500000000000000000000000)⟩ else
  if n = 15426 then ⟨(1085628551703200713369/1000000000000000000000000), (594592107199161795973837/1000000000000000000000000), (355285071854719/62500000000000000000000)⟩ else
  if n = 15427 then ⟨(542802911691317758801/500000000000000000000000), (594582722079713926396713/1000000000000000000000000), (5683604856808083/1000000000000000000000000)⟩ else
  if n = 15428 then ⟨(1085583099981009185477/1000000000000000000000000), (14864333453848231028233/25000000000000000000000), (355165549302637/62500000000000000000000)⟩ else
  if n = 15429 then ⟨(542780190748463593013/500000000000000000000000), (23782558216862601827213/40000000000000000000000), (5681692945709893/1000000000000000000000000)⟩ else
  if n = 15430 then ⟨(135692208491124519911/125000000000000000000000), (37159660867648671585333/62500000000000000000000), (5680737327343301/1000000000000000000000000)⟩ else
  if n = 15431 then ⟨(1085514959275823250497/1000000000000000000000000), (37159074596007984718809/62500000000000000000000), (1419945483418639/250000000000000000000000)⟩ else
  if n = 15432 then ⟨(1085492255536015777801/1000000000000000000000000), (594535814382569712078429/1000000000000000000000000), (567882676463581/100000000000000000000000)⟩ else
  if n = 15433 then ⟨(542734778354090948241/500000000000000000000000), (297263218210731023717827/500000000000000000000000), (709733977519907/125000000000000000000000)⟩ else
  if n = 15434 then ⟨(542723431395465133151/500000000000000000000000), (297258529826281277242131/500000000000000000000000), (5676917100177109/1000000000000000000000000)⟩ else
  if n = 15435 then ⟨(271356043445717512817/250000000000000000000000), (594507684075628869636151/1000000000000000000000000), (1418990651155403/250000000000000000000000)⟩ else
  if n = 15436 then ⟨(542700744841304962393/500000000000000000000000), (118899661938083760555323/200000000000000000000000), (1418752083356249/250000000000000000000000)⟩ else
  if n = 15437 then ⟨(1085378810488760391183/1000000000000000000000000), (118897787299338055368101/200000000000000000000000), (354628392907473/62500000000000000000000)⟩ else
  if n = 15438 then ⟨(217071227239986425307/200000000000000000000000), (118895912898840230496431/200000000000000000000000), (2836550231918823/500000000000000000000000)⟩ else
  if n = 15439 then ⟨(108533346681473531673/100000000000000000000000), (148617548420677364493797/250000000000000000000000), (2836073432655769/500000000000000000000000)⟩ else
  if n = 15440 then ⟨(1085310802331782307411/1000000000000000000000000), (297230412030986629721083/500000000000000000000000), (141779837271841/25000000000000000000000)⟩ else
  if n = 15441 then ⟨(1085288142749684291483/1000000000000000000000000), (118890291126350130112731/200000000000000000000000), (5670240340456309/1000000000000000000000000)⟩ else
  if n = 15442 then ⟨(1695727325104771293/1562500000000000000000), (594442088391799869049217/1000000000000000000000000), (1417321853497989/250000000000000000000000)⟩ else
  if n = 15443 then ⟨(1085242838282503838279/1000000000000000000000000), (148608180585469803132031/250000000000000000000000), (70854183892663/12500000000000000000000)⟩ else
  if n = 15444 then ⟨(542610096697323812993/500000000000000000000000), (594423357481746945771029/1000000000000000000000000), (5667382232651997/1000000000000000000000000)⟩ else
  if n = 15445 then ⟨(1085197553402099187491/1000000000000000000000000), (148603498452790377848939/250000000000000000000000), (1416607494410331/250000000000000000000000)⟩ else
  if n = 15446 then ⟨(1085174918303472891009/1000000000000000000000000), (118880926265976271488783/200000000000000000000000), (5665477946313533/1000000000000000000000000)⟩ else
  if n = 15447 then ⟨(1085152288097383276503/1000000000000000000000000), (594395270037665065537829/1000000000000000000000000), (1416131534650287/250000000000000000000000)⟩ else
  if n = 15448 then ⟨(271282415695611511549/250000000000000000000000), (594385909934271160868737/1000000000000000000000000), (707946819304593/125000000000000000000000)⟩ else
  if n = 15449 then ⟨(271276760589319103377/250000000000000000000000), (297188275509729180547349/500000000000000000000000), (1415655798438221/250000000000000000000000)⟩ else
  if n = 15450 then ⟨(271271106705122770861/250000000000000000000000), (594367193292985420265881/1000000000000000000000000), (1132334411296439/200000000000000000000000)⟩ else
  ⟨(271265454042676650537/250000000000000000000000), (594357836754611093372201/1000000000000000000000000), (5660721142557301/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15377 ≤ n) (hb : n ≤ 15451) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15377
  · exact row_15378
  · exact row_15379
  · exact row_15380
  · exact row_15381
  · exact row_15382
  · exact row_15383
  · exact row_15384
  · exact row_15385
  · exact row_15386
  · exact row_15387
  · exact row_15388
  · exact row_15389
  · exact row_15390
  · exact row_15391
  · exact row_15392
  · exact row_15393
  · exact row_15394
  · exact row_15395
  · exact row_15396
  · exact row_15397
  · exact row_15398
  · exact row_15399
  · exact row_15400
  · exact row_15401
  · exact row_15402
  · exact row_15403
  · exact row_15404
  · exact row_15405
  · exact row_15406
  · exact row_15407
  · exact row_15408
  · exact row_15409
  · exact row_15410
  · exact row_15411
  · exact row_15412
  · exact row_15413
  · exact row_15414
  · exact row_15415
  · exact row_15416
  · exact row_15417
  · exact row_15418
  · exact row_15419
  · exact row_15420
  · exact row_15421
  · exact row_15422
  · exact row_15423
  · exact row_15424
  · exact row_15425
  · exact row_15426
  · exact row_15427
  · exact row_15428
  · exact row_15429
  · exact row_15430
  · exact row_15431
  · exact row_15432
  · exact row_15433
  · exact row_15434
  · exact row_15435
  · exact row_15436
  · exact row_15437
  · exact row_15438
  · exact row_15439
  · exact row_15440
  · exact row_15441
  · exact row_15442
  · exact row_15443
  · exact row_15444
  · exact row_15445
  · exact row_15446
  · exact row_15447
  · exact row_15448
  · exact row_15449
  · exact row_15450
  · exact row_15451

end BstLean.Part271.R3.Rows15377
