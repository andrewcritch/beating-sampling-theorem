import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 16102–16128. -/
namespace BstLean.Part271.R3.Rows16102
open Real BstLean.Part130 BstLean.Part227

theorem width_16102 : mW 16102 = 529760261851034 := by
  have hu : mW 16102 ≤ 529760261851034 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16102 ≤ 529760261851033 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16102 : RowArithmetic 16102 (214263799500180592141/200000000000000000000000) (117701643877363167663109/200000000000000000000000) (5086141267351607/1000000000000000000000000) where
  r0 := (489418370291/1000000000000000000)
  k0 := (82683510206101/25000000000000000)
  k6 := (10790975956402907/1000000000000000000)
  q := (44863682416850269069/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16102]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16102]

theorem width_16103 : mW 16103 = 529875421760341 := by
  have hu : mW 16103 ≤ 529875421760341 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16103 ≤ 529875421760340 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16103 : RowArithmetic 16103 (1071299299721989402819/1000000000000000000000000) (294249794547095220775271/500000000000000000000000) (2542661354242183/500000000000000000000000) where
  r0 := (489372781509/1000000000000000000)
  k0 := (1653593183549551/500000000000000000)
  k6 := (2697660222539433/250000000000000000)
  q := (179460302016908463689/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16103]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16103]

theorem width_16104 : mW 16104 = 529990599549677 := by
  have hu : mW 16104 ≤ 529990599549677 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16104 ≤ 529990599549676 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16104 : RowArithmetic 16104 (1071279606021411164367/1000000000000000000000000) (588490959845490618659137/1000000000000000000000000) (2542252166902809/500000000000000000000000) where
  r0 := (122331799951/250000000000000000)
  k0 := (20668952141833/6250000000000000)
  k6 := (10790305855122639/1000000000000000000)
  q := (179465874193396444727/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16104]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16104]

theorem width_16105 : mW 16105 = 530105795220710 := by
  have hu : mW 16105 ≤ 530105795220710 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16105 ≤ 530105795220709 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16105 : RowArithmetic 16105 (1071259916398061765419/1000000000000000000000000) (294241165820257287836719/500000000000000000000000) (5083686143262119/1000000000000000000000000) where
  r0 := (19571265007/40000000000000000)
  k0 := (661375667005107/200000000000000000)
  k6 := (674373178205799/62500000000000000)
  q := (44867861549220283739/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16105]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16105]

theorem width_16106 : mW 16106 = 530221008775104 := by
  have hu : mW 16106 ≤ 530221008775104 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16106 ≤ 530221008775103 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16106 : RowArithmetic 16106 (53562011542541807331/50000000000000000000000) (73559213059882553129951/125000000000000000000000) (2541434068400341/500000000000000000000000) where
  r0 := (24461802881/50000000000000000)
  k0 := (1653362172045723/500000000000000000)
  k6 := (5394817939331661/500000000000000000)
  q := (89738509013689323721/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16106]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16106]

theorem width_16107 : mW 16107 = 530336240214524 := by
  have hu : mW 16107 ≤ 530336240214524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16107 ≤ 530336240214523 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16107 : RowArithmetic 16107 (107122054937862937283/100000000000000000000000) (588465078360926481200529/1000000000000000000000000) (5082050314368131/1000000000000000000000000) where
  r0 := (489190497137/1000000000000000000)
  k0 := (25832581014739/7812500000000000)
  k6 := (2697325234307353/250000000000000000)
  q := (179482589684905092747/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16107]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16107]

theorem width_16108 : mW 16108 = 530451489540637 := by
  have hu : mW 16108 ≤ 530451489540637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16108 ≤ 530451489540636 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16108 : RowArithmetic 16108 (267800217995084093663/250000000000000000000000) (294228226642955504474169/500000000000000000000000) (5081232675911289/1000000000000000000000000) where
  r0 := (19565797749/40000000000000000)
  k0 := (330641641240993/100000000000000000)
  k6 := (2697241506746553/250000000000000000)
  q := (22436020146184572367/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16108]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16108]

theorem width_16109 : mW 16109 = 530566756755108 := by
  have hu : mW 16109 ≤ 530566756755108 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16109 ≤ 530566756755107 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16109 : RowArithmetic 16109 (133897649831856622987/125000000000000000000000) (588447829253812403129133/1000000000000000000000000) (5080415221377017/1000000000000000000000000) where
  r0 := (489099397383/1000000000000000000)
  k0 := (1653131235830209/500000000000000000)
  k6 := (134857889349111/12500000000000000)
  q := (17949373248110921157/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16109]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16109]

theorem width_16110 : mW 16110 = 530682041859603 := by
  have hu : mW 16110 ≤ 530682041859603 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16110 ≤ 530682041859602 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16110 : RowArithmetic 16110 (1071161529401075156727/1000000000000000000000000) (73554900783053626849739/125000000000000000000000) (5079597950712187/1000000000000000000000000) where
  r0 := (122263464527/250000000000000000)
  k0 := (13224434190521/4000000000000000)
  k6 := (10788296300052577/1000000000000000000)
  q := (35899860723963818743/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16110]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16110]

theorem width_16111 : mW 16111 = 530797344855789 := by
  have hu : mW 16111 ≤ 530797344855789 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16111 ≤ 530797344855788 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16111 : RowArithmetic 16111 (26778546605447474349/25000000000000000000000) (18388455759923729453143/31250000000000000000000) (5078780863863679/1000000000000000000000000) where
  r0 := (4890083259/10000000000000000)
  k0 := (826488660080441/250000000000000000)
  k6 := (5393980741676233/500000000000000000)
  q := (35900974917124465187/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16111]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16111]

theorem width_16112 : mW 16112 = 530912665745330 := by
  have hu : mW 16112 ≤ 530912665745330 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16112 ≤ 530912665745329 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16112 : RowArithmetic 16112 (535561101552110837469/500000000000000000000000) (588421963413001910345549/1000000000000000000000000) (2538981980389211/500000000000000000000000) where
  r0 := (488962800757/1000000000000000000)
  k0 := (3305800749730533/1000000000000000000)
  k6 := (10787626697823707/1000000000000000000)
  q := (179510445378535006297/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16112]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16112]

theorem width_16113 : mW 16113 = 531028004529893 := by
  have hu : mW 16113 ≤ 531028004529893 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16113 ≤ 531028004529892 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16113 : RowArithmetic 16113 (33471954564341878317/31250000000000000000000) (588413343550555278090901/1000000000000000000000000) (1015429448280667/200000000000000000000000) where
  r0 := (488917282677/1000000000000000000)
  k0 := (3305646875852131/1000000000000000000)
  k6 := (2157458388692293/200000000000000000)
  q := (179516015998573230369/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16113]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16113]

theorem width_16114 : mW 16114 = 531143361211143 := by
  have hu : mW 16114 ≤ 531143361211143 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16114 ≤ 531143361211142 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16114 : RowArithmetic 16114 (267770723270238003369/250000000000000000000000) (294202362365009036821123/500000000000000000000000) (39658833638167/7812500000000000000000) where
  r0 := (488871771659/1000000000000000000)
  k0 := (3305493018685511/1000000000000000000)
  k6 := (2157391444052181/200000000000000000)
  q := (179521586445753091223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16114]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16114]

theorem width_16115 : mW 16115 = 531258735790748 := by
  have hu : mW 16115 ≤ 531258735790748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16115 ≤ 531258735790747 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16115 : RowArithmetic 16115 (6694145276057217191/6250000000000000000000) (588396106951188923678813/1000000000000000000000000) (2537757176785747/500000000000000000000000) where
  r0 := (488826267701/1000000000000000000)
  k0 := (1652669589113123/500000000000000000)
  k6 := (1348327816027149/125000000000000000)
  q := (89763578360045339717/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16115]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16115]

theorem width_16116 : mW 16116 = 531374128270373 := by
  have hu : mW 16116 ≤ 531374128270373 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16116 ≤ 531374128270372 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16116 : RowArithmetic 16116 (26776089983061170703/25000000000000000000000) (294193745106933300563189/500000000000000000000000) (5074698185008683/1000000000000000000000000) where
  r0 := (244390385401/500000000000000000)
  k0 := (1652592677236643/500000000000000000)
  k6 := (2696571966831373/250000000000000000)
  q := (4488318170540052077/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16116]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16116]

theorem width_16117 : mW 16117 = 531489538651684 := by
  have hu : mW 16117 ≤ 531489538651684 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16117 ≤ 531489538651683 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16117 : RowArithmetic 16117 (1071023958539726880683/1000000000000000000000000) (588378874517849945416033/1000000000000000000000000) (5073882199943951/1000000000000000000000000) where
  r0 := (1527297753/3125000000000000)
  k0 := (3305031547422203/1000000000000000000)
  k6 := (5392976618790487/500000000000000000)
  q := (5610571773446980867/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16117]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16117]

theorem width_16118 : mW 16118 = 531604966936348 := by
  have hu : mW 16118 ≤ 531604966936348 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16118 ≤ 531604966936347 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16118 : RowArithmetic 16118 (535502160909946833439/500000000000000000000000) (147092564965734422228709/250000000000000000000000) (5073066398324311/1000000000000000000000000) where
  r0 := (244344899087/500000000000000000)
  k0 := (3304877757071947/1000000000000000000)
  k6 := (10785618638978807/1000000000000000000)
  q := (35908773301242135303/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16118]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16118]

theorem width_16119 : mW 16119 = 531720413126030 := by
  have hu : mW 16119 ≤ 531720413126030 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16119 ≤ 531720413126029 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16119 : RowArithmetic 16119 (535492344580923421479/500000000000000000000000) (117672329249785754957093/200000000000000000000000) (2536125390048409/500000000000000000000000) where
  r0 := (488644322441/1000000000000000000)
  k0 := (660944796682941/200000000000000000)
  k6 := (10785284071514159/1000000000000000000)
  q := (35909887217868005997/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16119]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16119]

theorem width_16120 : mW 16120 = 531835877222397 := by
  have hu : mW 16120 ≤ 531835877222397 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16120 ≤ 531835877222396 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16120 : RowArithmetic 16120 (535482530282242965549/500000000000000000000000) (588353033675622124651683/1000000000000000000000000) (1267858836302131/250000000000000000000000) where
  r0 := (244299426881/500000000000000000)
  k0 := (826142556614047/250000000000000000)
  k6 := (10784949535182203/1000000000000000000)
  q := (35911001099941505251/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16120]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16120]

theorem width_16121 : mW 16121 = 531951359227116 := by
  have hu : mW 16121 ≤ 531951359227116 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16121 ≤ 531951359227115 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16121 : RowArithmetic 16121 (214189087205342167053/200000000000000000000000) (147086105535704191525987/250000000000000000000000) (633827511700813/125000000000000000000000) where
  r0 := (488553392133/1000000000000000000)
  k0 := (3304416486185201/1000000000000000000)
  k6 := (10784615029978109/1000000000000000000)
  q := (179560574737329240929/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16121]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16121]

theorem width_16122 : mW 16122 = 532066859141853 := by
  have hu : mW 16122 ≤ 532066859141853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16122 ≤ 532066859141852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16122 : RowArithmetic 16122 (1070925815547422098519/1000000000000000000000000) (147083952912577936624847/250000000000000000000000) (2534902512618929/500000000000000000000000) where
  r0 := (244253968777/500000000000000000)
  k0 := (3304262762604073/1000000000000000000)
  k6 := (2696070138974263/250000000000000000)
  q := (89783071901110623561/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16122]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16122]

theorem width_16123 : mW 16123 = 532182376968274 := by
  have hu : mW 16123 ≤ 532182376968274 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16123 ≤ 532182376968273 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16123 : RowArithmetic 16123 (1070906199125520644999/1000000000000000000000000) (117665440439581219729459/200000000000000000000000) (5068990140049707/1000000000000000000000000) where
  r0 := (488462490023/1000000000000000000)
  k0 := (330410905570837/100000000000000000)
  k6 := (2156789222586841/200000000000000000)
  q := (179571712694399615453/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16123]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16123]

theorem width_16124 : mW 16124 = 532297912708046 := by
  have hu : mW 16124 ≤ 532297912708046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16124 ≤ 532297912708045 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16124 : RowArithmetic 16124 (42835463470396300899/40000000000000000000000) (588318593785399098666017/1000000000000000000000000) (5068175437989181/1000000000000000000000000) where
  r0 := (244208524769/500000000000000000)
  k0 := (1651977682746827/500000000000000000)
  k6 := (10783611701084743/1000000000000000000)
  q := (179577281413880414051/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16124]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16124]

theorem width_16125 : mW 16125 = 532413466362836 := by
  have hu : mW 16125 ≤ 532413466362836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16125 ≤ 532413466362835 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16125 : RowArithmetic 16125 (1070866978449484159827/1000000000000000000000000) (58830998641258988450349/100000000000000000000000) (1266840229750857/250000000000000000000000) where
  r0 := (488371616099/1000000000000000000)
  k0 := (1651900845981127/500000000000000000)
  k6 := (5391638660171921/500000000000000000)
  q := (89791424980339854277/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16125]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16125]

theorem width_16126 : mW 16126 = 532529037934310 := by
  have hu : mW 16126 ≤ 532529037934310 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16126 ≤ 532529037934309 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16126 : RowArithmetic 16126 (107084737419315262397/100000000000000000000000) (588301380079277691546431/1000000000000000000000000) (1266636645759907/250000000000000000000000) where
  r0 := (244163094851/500000000000000000)
  k0 := (412956004387871/125000000000000000)
  k6 := (269573574267667/25000000000000000)
  q := (179588418334813562109/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16126]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16126]

theorem width_16127 : mW 16127 = 532644627424135 := by
  have hu : mW 16127 ≤ 532644627424135 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16127 ≤ 532644627424134 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16127 : RowArithmetic 16127 (16731683968590861019/15625000000000000000000) (147073193696315476453161/250000000000000000000000) (633216553755621/125000000000000000000000) where
  r0 := (122070192587/250000000000000000)
  k0 := (660698878984301/200000000000000000)
  k6 := (2156521730433687/200000000000000000)
  q := (179593986536298035371/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16127]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16127]

theorem width_16128 : mW 16128 = 532760234833977 := by
  have hu : mW 16128 ≤ 532760234833977 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 16128 ≤ 532760234833976 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_16128 : RowArithmetic 16128 (133851022229796803923/125000000000000000000000) (147071042632585468785981/250000000000000000000000) (5064918459966663/1000000000000000000000000) where
  r0 := (244117679017/500000000000000000)
  k0 := (825835192852511/250000000000000000)
  k6 := (2156454872944857/200000000000000000)
  q := (179599554565149186509/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_16128]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_16128]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 16102 then ⟨(214263799500180592141/200000000000000000000000), (117701643877363167663109/200000000000000000000000), (5086141267351607/1000000000000000000000000)⟩ else
  if n = 16103 then ⟨(1071299299721989402819/1000000000000000000000000), (294249794547095220775271/500000000000000000000000), (2542661354242183/500000000000000000000000)⟩ else
  if n = 16104 then ⟨(1071279606021411164367/1000000000000000000000000), (588490959845490618659137/1000000000000000000000000), (2542252166902809/500000000000000000000000)⟩ else
  if n = 16105 then ⟨(1071259916398061765419/1000000000000000000000000), (294241165820257287836719/500000000000000000000000), (5083686143262119/1000000000000000000000000)⟩ else
  if n = 16106 then ⟨(53562011542541807331/50000000000000000000000), (73559213059882553129951/125000000000000000000000), (2541434068400341/500000000000000000000000)⟩ else
  if n = 16107 then ⟨(107122054937862937283/100000000000000000000000), (588465078360926481200529/1000000000000000000000000), (5082050314368131/1000000000000000000000000)⟩ else
  if n = 16108 then ⟨(267800217995084093663/250000000000000000000000), (294228226642955504474169/500000000000000000000000), (5081232675911289/1000000000000000000000000)⟩ else
  if n = 16109 then ⟨(133897649831856622987/125000000000000000000000), (588447829253812403129133/1000000000000000000000000), (5080415221377017/1000000000000000000000000)⟩ else
  if n = 16110 then ⟨(1071161529401075156727/1000000000000000000000000), (73554900783053626849739/125000000000000000000000), (5079597950712187/1000000000000000000000000)⟩ else
  if n = 16111 then ⟨(26778546605447474349/25000000000000000000000), (18388455759923729453143/31250000000000000000000), (5078780863863679/1000000000000000000000000)⟩ else
  if n = 16112 then ⟨(535561101552110837469/500000000000000000000000), (588421963413001910345549/1000000000000000000000000), (2538981980389211/500000000000000000000000)⟩ else
  if n = 16113 then ⟨(33471954564341878317/31250000000000000000000), (588413343550555278090901/1000000000000000000000000), (1015429448280667/200000000000000000000000)⟩ else
  if n = 16114 then ⟨(267770723270238003369/250000000000000000000000), (294202362365009036821123/500000000000000000000000), (39658833638167/7812500000000000000000)⟩ else
  if n = 16115 then ⟨(6694145276057217191/6250000000000000000000), (588396106951188923678813/1000000000000000000000000), (2537757176785747/500000000000000000000000)⟩ else
  if n = 16116 then ⟨(26776089983061170703/25000000000000000000000), (294193745106933300563189/500000000000000000000000), (5074698185008683/1000000000000000000000000)⟩ else
  if n = 16117 then ⟨(1071023958539726880683/1000000000000000000000000), (588378874517849945416033/1000000000000000000000000), (5073882199943951/1000000000000000000000000)⟩ else
  if n = 16118 then ⟨(535502160909946833439/500000000000000000000000), (147092564965734422228709/250000000000000000000000), (5073066398324311/1000000000000000000000000)⟩ else
  if n = 16119 then ⟨(535492344580923421479/500000000000000000000000), (117672329249785754957093/200000000000000000000000), (2536125390048409/500000000000000000000000)⟩ else
  if n = 16120 then ⟨(535482530282242965549/500000000000000000000000), (588353033675622124651683/1000000000000000000000000), (1267858836302131/250000000000000000000000)⟩ else
  if n = 16121 then ⟨(214189087205342167053/200000000000000000000000), (147086105535704191525987/250000000000000000000000), (633827511700813/125000000000000000000000)⟩ else
  if n = 16122 then ⟨(1070925815547422098519/1000000000000000000000000), (147083952912577936624847/250000000000000000000000), (2534902512618929/500000000000000000000000)⟩ else
  if n = 16123 then ⟨(1070906199125520644999/1000000000000000000000000), (117665440439581219729459/200000000000000000000000), (5068990140049707/1000000000000000000000000)⟩ else
  if n = 16124 then ⟨(42835463470396300899/40000000000000000000000), (588318593785399098666017/1000000000000000000000000), (5068175437989181/1000000000000000000000000)⟩ else
  if n = 16125 then ⟨(1070866978449484159827/1000000000000000000000000), (58830998641258988450349/100000000000000000000000), (1266840229750857/250000000000000000000000)⟩ else
  if n = 16126 then ⟨(107084737419315262397/100000000000000000000000), (588301380079277691546431/1000000000000000000000000), (1266636645759907/250000000000000000000000)⟩ else
  if n = 16127 then ⟨(16731683968590861019/15625000000000000000000), (147073193696315476453161/250000000000000000000000), (633216553755621/125000000000000000000000)⟩ else
  ⟨(133851022229796803923/125000000000000000000000), (147071042632585468785981/250000000000000000000000), (5064918459966663/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 16102 ≤ n) (hb : n ≤ 16128) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_16102
  · exact row_16103
  · exact row_16104
  · exact row_16105
  · exact row_16106
  · exact row_16107
  · exact row_16108
  · exact row_16109
  · exact row_16110
  · exact row_16111
  · exact row_16112
  · exact row_16113
  · exact row_16114
  · exact row_16115
  · exact row_16116
  · exact row_16117
  · exact row_16118
  · exact row_16119
  · exact row_16120
  · exact row_16121
  · exact row_16122
  · exact row_16123
  · exact row_16124
  · exact row_16125
  · exact row_16126
  · exact row_16127
  · exact row_16128

end BstLean.Part271.R3.Rows16102
