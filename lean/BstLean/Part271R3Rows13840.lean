import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13840–13914. -/
namespace BstLean.Part271.R3.Rows13840
open Real BstLean.Part130 BstLean.Part227

theorem width_13840 : mW 13840 = 311871949773400 := by
  have hu : mW 13840 ≤ 311871949773400 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13840 ≤ 311871949773399 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13840 : RowArithmetic 13840 (1128943450346675729891/1000000000000000000000000) (24446439888348531820729/40000000000000000000000) (3768600833154149/500000000000000000000000) where
  r0 := (153545068849/250000000000000000)
  k0 := (3704987065443091/1000000000000000000)
  k6 := (11639453535828767/1000000000000000000)
  q := (166373074744683371799/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13840]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13840]

theorem width_13841 : mW 13841 = 311950826248433 := by
  have hu : mW 13841 ≤ 311950826248433 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13841 ≤ 311950826248432 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13841 : RowArithmetic 13841 (1128910777770578274917/1000000000000000000000000) (611149361036338842166841/1000000000000000000000000) (1883945777413779/250000000000000000000000) where
  r0 := (307056857813/500000000000000000)
  k0 := (926196575525449/250000000000000000)
  k6 := (11639033058125621/1000000000000000000)
  q := (166379085224074963959/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13841]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13841]

theorem width_13842 : mW 13842 = 312029716971642 := by
  have hu : mW 13842 ≤ 312029716971642 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13842 ≤ 312029716971641 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13842 : RowArithmetic 13842 (564439056552611542071/500000000000000000000000) (611137726547020425315551/1000000000000000000000000) (7534364926137179/1000000000000000000000000) where
  r0 := (307023583939/500000000000000000)
  k0 := (92614639103631/25000000000000000)
  k6 := (11638612625988719/1000000000000000000)
  q := (166385095486344569397/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13842]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13842]

theorem width_13843 : mW 13843 = 312108621944570 := by
  have hu : mW 13843 ≤ 312108621944570 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13843 ≤ 312108621944569 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13843 : RowArithmetic 13843 (70552841021756494291/62500000000000000000000) (611126093740369218722813/1000000000000000000000000) (301317884625141/40000000000000000000000) where
  r0 := (613980632147/1000000000000000000)
  k0 := (3704384851562463/1000000000000000000)
  k6 := (1454774029926229/125000000000000000)
  q := (166391105531515716293/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13843]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13843]

theorem width_13844 : mW 13844 = 312187541168762 := by
  have hu : mW 13844 ≤ 312187541168762 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13844 ≤ 312187541168761 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13844 : RowArithmetic 13844 (564406403748357132393/500000000000000000000000) (61111446261599638981739/100000000000000000000000) (3765764839001597/500000000000000000000000) where
  r0 := (38369631777/62500000000000000)
  k0 := (148167366574183/40000000000000000)
  k6 := (2909442974595183/250000000000000000)
  q := (166397115359611928581/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13844]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13844]

theorem width_13845 : mW 13845 = 312266474645763 := by
  have hu : mW 13845 ≤ 312266474645763 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13845 ≤ 312266474645762 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13845 : RowArithmetic 13845 (1128780166548548685443/1000000000000000000000000) (611102833173513418776047/1000000000000000000000000) (94126407664191/12500000000000000000000) where
  r0 := (76730949591/125000000000000000)
  k0 := (740796700502123/200000000000000000)
  k6 := (5818675801446597/500000000000000000)
  q := (83201562485328362973/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13845]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13845]

theorem width_13846 : mW 13846 = 312345422377115 := by
  have hu : mW 13846 ≤ 312345422377115 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13846 ≤ 312345422377114 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13846 : RowArithmetic 13846 (28218688337527614817/25000000000000000000000) (305545602706265887393601/500000000000000000000000) (7528695920899003/1000000000000000000000000) where
  r0 := (306890548517/500000000000000000)
  k0 := (462972858253961/125000000000000000)
  k6 := (2909232838234749/250000000000000000)
  q := (83204567182336811913/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13846]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13846]

theorem width_13847 : mW 13847 = 312424384364365 := by
  have hu : mW 13847 ≤ 312424384364365 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13847 ≤ 312424384364364 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13847 : RowArithmetic 13847 (1128714908351877300417/1000000000000000000000000) (611079579332663046536507/1000000000000000000000000) (7527279601168517/1000000000000000000000000) where
  r0 := (122742921869/200000000000000000)
  k0 := (3703582254906829/1000000000000000000)
  k6 := (2327302229701983/200000000000000000)
  q := (33283028708337226683/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13847]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13847]

theorem width_13848 : mW 13848 = 312503360609056 := by
  have hu : mW 13848 ≤ 312503360609056 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13848 ≤ 312503360609055 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13848 : RowArithmetic 13848 (141085286387295704377/125000000000000000000000) (305533977466759502527451/500000000000000000000000) (7525863653818123/1000000000000000000000000) where
  r0 := (30682406683/50000000000000000)
  k0 := (1851690834568571/500000000000000000)
  k6 := (2327218197919547/200000000000000000)
  q := (166421152501717761659/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13848]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13848]

theorem width_13849 : mW 13849 = 312582351112732 := by
  have hu : mW 13849 ≤ 312582351112732 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13849 ≤ 312582351112731 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13849 : RowArithmetic 13849 (1128649681738068811623/1000000000000000000000000) (9547755190854868663241/15625000000000000000000) (7524448078722153/1000000000000000000000000) where
  r0 := (306790834987/500000000000000000)
  k0 := (1851590554355829/500000000000000000)
  k6 := (2908917719048559/250000000000000000)
  q := (325053049306234397/1953125000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13849]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13849]

theorem width_13850 : mW 13850 = 312661355876939 := by
  have hu : mW 13850 ≤ 312661355876939 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13850 ≤ 312661355876938 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13850 : RowArithmetic 13850 (225723416053697162327/200000000000000000000000) (305522355587926347727243/500000000000000000000000) (7523032875754943/1000000000000000000000000) where
  r0 := (122703043657/200000000000000000)
  k0 := (3702980573628459/1000000000000000000)
  k6 := (5817625404145603/500000000000000000)
  q := (16643316977093238069/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13850]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13850]

theorem width_13851 : mW 13851 = 312740374903221 := by
  have hu : mW 13851 ≤ 312740374903221 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13851 ≤ 312740374903220 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13851 : RowArithmetic 13851 (1128584486687117877001/1000000000000000000000000) (305516545908277231001633/500000000000000000000000) (7521618044790929/1000000000000000000000000) where
  r0 := (61344877859/100000000000000000)
  k0 := (370278006388261/100000000000000000)
  k6 := (11634830785880431/1000000000000000000)
  q := (166439178080162364157/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13851]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13851]

theorem width_13852 : mW 13852 = 312819408193123 := by
  have hu : mW 13852 ≤ 312819408193123 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13852 ≤ 312819408193122 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13852 : RowArithmetic 13852 (1128551900991466638697/1000000000000000000000000) (7637768426705364904141/12500000000000000000000) (7520203585704579/1000000000000000000000000) where
  r0 := (306691175443/500000000000000000)
  k0 := (3702579579469171/1000000000000000000)
  k6 := (11634410808953701/1000000000000000000)
  q := (83222593086252725823/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13852]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13852]

theorem width_13853 : mW 13853 = 312898455748188 := by
  have hu : mW 13853 ≤ 312898455748188 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13853 ≤ 312898455748187 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13853 : RowArithmetic 13853 (282129830794758996273/250000000000000000000000) (611009858135089173548309/1000000000000000000000000) (375939474918523/50000000000000000000000) where
  r0 := (613315935169/1000000000000000000)
  k0 := (740475824076037/200000000000000000)
  k6 := (11633990877502807/1000000000000000000)
  q := (2600799906999767639/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13853]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13853]

theorem width_13854 : mW 13854 = 312977517569963 := by
  have hu : mW 13854 ≤ 312977517569963 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13854 ≤ 312977517569962 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13854 : RowArithmetic 13854 (564243376623664162603/500000000000000000000000) (610998243812146961107581/1000000000000000000000000) (7517375782663097/1000000000000000000000000) where
  r0 := (613249531437/1000000000000000000)
  k0 := (3702178686613729/1000000000000000000)
  k6 := (11633570991519543/1000000000000000000)
  q := (166457201706624877409/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13854]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13854]

theorem width_13855 : mW 13855 = 313056593659992 := by
  have hu : mW 13855 ≤ 313056593659992 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13855 ≤ 313056593659991 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13855 : RowArithmetic 13855 (225690838238769789489/200000000000000000000000) (305493315583607529765419/500000000000000000000000) (7515962438457139/1000000000000000000000000) where
  r0 := (613183139687/1000000000000000000)
  k0 := (3701978278164859/1000000000000000000)
  k6 := (1454143893874463/125000000000000000)
  q := (3329264182968963489/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13855]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13855]

theorem width_13856 : mW 13856 = 313135684019819 := by
  have hu : mW 13856 ≤ 313135684019819 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13856 ≤ 313135684019818 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13856 : RowArithmetic 13856 (564210818508052074959/500000000000000000000000) (76371877524988288928463/125000000000000000000000) (939318683203411/125000000000000000000000) where
  r0 := (153279189979/250000000000000000)
  k0 := (3701777895028631/1000000000000000000)
  k6 := (11632731355923089/1000000000000000000)
  q := (166469216373478493047/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13856]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13856]

theorem width_13857 : mW 13857 = 313214788650990 := by
  have hu : mW 13857 ≤ 313214788650990 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13857 ≤ 313214788650989 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13857 : RowArithmetic 13857 (282097272677899999237/250000000000000000000000) (610963410909833522796029/1000000000000000000000000) (7513136864048251/1000000000000000000000000) where
  r0 := (15326259803/25000000000000000)
  k0 := (92539438429927/25000000000000000)
  k6 := (1454038950786687/125000000000000000)
  q := (166475223381739301993/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13857]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13857]

theorem width_13858 : mW 13858 = 313293907555050 := by
  have hu : mW 13858 ≤ 313293907555050 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13858 ≤ 313293907555049 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13858 : RowArithmetic 13858 (70522284517365261551/62500000000000000000000) (305475901648304831481449/500000000000000000000000) (3755862316797407/500000000000000000000000) where
  r0 := (76623004537/125000000000000000)
  k0 := (3701377204665259/1000000000000000000)
  k6 := (11631891902098729/1000000000000000000)
  q := (166481230173254065849/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13858]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13858]

theorem width_13859 : mW 13859 = 313373040733543 := by
  have hu : mW 13859 ≤ 313373040733543 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13859 ≤ 313373040733542 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13859 : RowArithmetic 13859 (564162010856173019963/500000000000000000000000) (76367524669980983667823/125000000000000000000000) (1877578193535459/250000000000000000000000) where
  r0 := (612917692443/1000000000000000000)
  k0 := (1850588448717127/500000000000000000)
  k6 := (1163147224333059/100000000000000000)
  q := (8324361837402312247/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13859]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13859]

theorem width_13860 : mW 13860 = 313452188188016 := by
  have hu : mW 13860 ≤ 313452188188016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13860 ≤ 313452188188015 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13860 : RowArithmetic 13860 (282072874753153508547/250000000000000000000000) (152732148274790332198749/250000000000000000000000) (7508901285564161/1000000000000000000000000) where
  r0 := (153212840139/250000000000000000)
  k0 := (3700976615493079/1000000000000000000)
  k6 := (5815526314990443/500000000000000000)
  q := (166493243106139295361/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13860]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13860]

theorem width_13861 : mW 13861 = 313531349920012 := by
  have hu : mW 13861 ≤ 313531349920012 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13861 ≤ 313531349920011 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13861 : RowArithmetic 13861 (1128258984176160131449/1000000000000000000000000) (61091699051416337033793/100000000000000000000000) (3753745083868389/500000000000000000000000) where
  r0 := (76598130079/125000000000000000)
  k0 := (1850388179418389/500000000000000000)
  k6 := (465225322481657/40000000000000000)
  q := (10406203077972291811/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13861]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13861]

theorem width_13862 : mW 13862 = 313610525931077 := by
  have hu : mW 13862 ≤ 313610525931077 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13862 ≤ 313610525931076 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13862 : RowArithmetic 13862 (112822647720049544053/100000000000000000000000) (305452694802233732225337/500000000000000000000000) (7506079420534659/1000000000000000000000000) where
  r0 := (612718732669/1000000000000000000)
  k0 := (3700576127463419/1000000000000000000)
  k6 := (5815106769752009/500000000000000000)
  q := (83252627586160906709/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13862]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13862]

theorem width_13863 : mW 13863 = 313689716222757 := by
  have hu : mW 13863 ≤ 313689716222757 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13863 ≤ 313689716222756 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13863 : RowArithmetic 13863 (70512123630195754897/62500000000000000000000) (305446895184843634216817/500000000000000000000000) (750466904383283/100000000000000000000000) where
  r0 := (76581554583/125000000000000000)
  k0 := (925093980342011/250000000000000000)
  k6 := (465191762494419/40000000000000000)
  q := (166511260880458172093/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13863]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13863]

theorem width_13864 : mW 13864 = 313768920796597 := by
  have hu : mW 13864 ≤ 313768920796597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13864 ≤ 313768920796596 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13864 : RowArithmetic 13864 (1128161486821583789063/1000000000000000000000000) (610882192809436361751347/1000000000000000000000000) (750325903750639/100000000000000000000000) where
  r0 := (153146538153/250000000000000000)
  k0 := (1850087870269829/500000000000000000)
  k6 := (2907343657650653/250000000000000000)
  q := (83258633185994592089/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13864]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13864]

theorem width_13865 : mW 13865 = 313848139654142 := by
  have hu : mW 13865 ≤ 313848139654142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13865 ≤ 313848139654141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13865 : RowArithmetic 13865 (564064501706682661407/500000000000000000000000) (610870596923328720511311/1000000000000000000000000) (3750924700715247/500000000000000000000000) where
  r0 := (612519880513/1000000000000000000)
  k0 := (92499389624559/25000000000000000)
  k6 := (2325791048844449/200000000000000000)
  q := (1332186173175506277/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13865]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13865]

theorem width_13866 : mW 13866 = 313927372796938 := by
  have hu : mW 13866 ≤ 313927372796938 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13866 ≤ 313927372796937 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13866 : RowArithmetic 13866 (11280965278559918161/10000000000000000000000) (610859002710978188657639/1000000000000000000000000) (300017605419213/40000000000000000000000) where
  r0 := (306226810181/500000000000000000)
  k0 := (3699775454685149/1000000000000000000)
  k6 := (11628535903211193/1000000000000000000)
  q := (83264638352664452079/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13866]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13866]

theorem width_13867 : mW 13867 = 314006620226529 := by
  have hu : mW 13867 ≤ 314006620226529 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13867 ≤ 314006620226528 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13867 : RowArithmetic 13867 (1128064060146980649159/1000000000000000000000000) (152711852542999729865027/250000000000000000000000) (1499806247906233/200000000000000000000000) where
  r0 := (153096843039/250000000000000000)
  k0 := (739915069928613/200000000000000000)
  k6 := (465124664302451/40000000000000000)
  q := (1040845509669902933/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13867]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13867]

theorem width_13868 : mW 13868 = 314085881944463 := by
  have hu : mW 13868 ≤ 314085881944463 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13868 ≤ 314085881944462 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13868 : RowArithmetic 13868 (1128031600283847731163/1000000000000000000000000) (610835819306005057733587/1000000000000000000000000) (3748811356729127/500000000000000000000000) where
  r0 := (612321135893/1000000000000000000)
  k0 := (1849687634927081/500000000000000000)
  k6 := (2325539471452863/200000000000000000)
  q := (41635321543132100567/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13868]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13868]

theorem width_13869 : mW 13869 = 314165157952283 := by
  have hu : mW 13869 ≤ 314165157952283 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13869 ≤ 314165157952282 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13869 : RowArithmetic 13869 (140999893533014133759/125000000000000000000000) (610824230112610927729681/1000000000000000000000000) (3748107278568503/500000000000000000000000) where
  r0 := (612254911569/1000000000000000000)
  k0 := (739835043062091/200000000000000000)
  k6 := (11627278152312137/1000000000000000000)
  q := (166547290581384121177/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13869]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13869]

theorem width_13870 : mW 13870 = 314244448251537 := by
  have hu : mW 13870 ≤ 314244448251537 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13870 ≤ 314244448251536 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13870 : RowArithmetic 13870 (1127966704085294584681/1000000000000000000000000) (610812642591431019755289/1000000000000000000000000) (1498961354088553/200000000000000000000000) where
  r0 := (306094349591/500000000000000000)
  k0 := (3698975186009999/1000000000000000000)
  k6 := (11626858992696567/1000000000000000000)
  q := (83276647386887519921/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13870]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13870]

theorem width_13871 : mW 13871 = 314323752843769 := by
  have hu : mW 13871 ≤ 314323752843769 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13871 ≤ 314323752843768 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13871 : RowArithmetic 13871 (70495891734057104443/62500000000000000000000) (610801056742079841003967/1000000000000000000000000) (299735974130041/40000000000000000000000) where
  r0 := (76515312341/125000000000000000)
  k0 := (1849387590972401/500000000000000000)
  k6 := (2325287975681887/200000000000000000)
  q := (83279649374862283939/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13871]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13871]

theorem width_13872 : mW 13872 = 314403071730526 := by
  have hu : mW 13872 ≤ 314403071730526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13872 ≤ 314403071730525 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13872 : RowArithmetic 13872 (563950919620245436981/500000000000000000000000) (152697368141043018357319/250000000000000000000000) (374599615271863/50000000000000000000000) where
  r0 := (153014077551/250000000000000000)
  k0 := (739715040621979/200000000000000000)
  k6 := (2906505202360643/250000000000000000)
  q := (83282651254628055339/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13872]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13872]

theorem width_13873 : mW 13873 = 314482404913353 := by
  have hu : mW 13873 ≤ 314482404913353 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13873 ≤ 314482404913352 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13873 : RowArithmetic 13873 (281967354642387244121/250000000000000000000000) (610777890057322585283683/1000000000000000000000000) (1872646406719261/250000000000000000000000) where
  r0 := (76498766701/125000000000000000)
  k0 := (115574226546979/31250000000000000)
  k6 := (11625601785787809/1000000000000000000)
  q := (8328565302619653471/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13873]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13873]

theorem width_13874 : mW 13874 = 314561752393796 := by
  have hu : mW 13874 ≤ 314561752393796 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13874 ≤ 314561752393795 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13874 : RowArithmetic 13874 (1127837005729611146063/1000000000000000000000000) (610766309221146256187629/1000000000000000000000000) (7489179317445983/1000000000000000000000000) where
  r0 := (76490496117/125000000000000000)
  k0 := (739635064223421/200000000000000000)
  k6 := (5812591403718491/500000000000000000)
  q := (33315461875831768213/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13874]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13874]

theorem width_13875 : mW 13875 = 314641114173401 := by
  have hu : mW 13875 ≤ 314641114173401 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13875 ≤ 314641114173400 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13875 : RowArithmetic 13875 (225560920143640310381/200000000000000000000000) (610754730055258153345413/1000000000000000000000000) (748777337701973/100000000000000000000000) where
  r0 := (122371563237/200000000000000000)
  k0 := (924493854486563/250000000000000000)
  k6 := (11624763874381929/1000000000000000000)
  q := (41645828122394204589/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13875]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13875]

theorem width_13876 : mW 13876 = 314720490253714 := by
  have hu : mW 13876 ≤ 314720490253714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13876 ≤ 314720490253713 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13876 : RowArithmetic 13876 (1127772203532845364491/1000000000000000000000000) (122148630511854691385429/200000000000000000000000) (1497273561094799/200000000000000000000000) where
  r0 := (611791675353/1000000000000000000)
  k0 := (924443884997203/250000000000000000)
  k6 := (11624344986614487/1000000000000000000)
  q := (2602958052869849841/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13876]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13876]

theorem width_13877 : mW 13877 = 314799880636281 := by
  have hu : mW 13877 ≤ 314799880636281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13877 ≤ 314799880636280 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13877 : RowArithmetic 13877 (1127739814171068755053/1000000000000000000000000) (15268289418320185837211/25000000000000000000000) (7484962602684537/1000000000000000000000000) where
  r0 := (152931386609/250000000000000000)
  k0 := (924393921809197/250000000000000000)
  k6 := (11623926144126499/1000000000000000000)
  q := (83297659030731469891/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13877]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13877]

theorem width_13878 : mW 13878 = 314879285322648 := by
  have hu : mW 13878 ≤ 314879285322648 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13878 ≤ 314879285322647 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13878 : RowArithmetic 13878 (281926858157599723763/250000000000000000000000) (305360001287737748510231/500000000000000000000000) (7483557768527171/1000000000000000000000000) where
  r0 := (611659429431/1000000000000000000)
  k0 := (1848687929842599/500000000000000000)
  k6 := (5811753673454903/500000000000000000)
  q := (33320264104595569667/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13878]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13878]

theorem width_13879 : mW 13879 = 314958704314362 := by
  have hu : mW 13879 ≤ 314958704314362 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13879 ≤ 314958704314361 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13879 : RowArithmetic 13879 (140959382363545417487/125000000000000000000000) (305354215043446617646313/500000000000000000000000) (7482153302877737/1000000000000000000000000) where
  r0 := (38224582771/62500000000000000)
  k0 := (3697176057332083/1000000000000000000)
  k6 := (363221518592383/31250000000000000)
  q := (166607322768238491373/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13879]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13879]

theorem width_13880 : mW 13880 = 315038137612969 := by
  have hu : mW 13880 ≤ 315038137612969 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13880 ≤ 315038137612968 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13880 : RowArithmetic 13880 (140955336625311407589/125000000000000000000000) (610696859266676286287163/1000000000000000000000000) (3740374602806077/500000000000000000000000) where
  r0 := (611527231147/1000000000000000000)
  k0 := (1848488140084719/500000000000000000)
  k6 := (5811334944128847/500000000000000000)
  q := (83306662398634120289/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13880]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13880]

theorem width_13881 : mW 13881 = 315117585220014 := by
  have hu : mW 13881 ≤ 315117585220014 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13881 ≤ 315117585220013 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13881 : RowArithmetic 13881 (225522066982062688507/200000000000000000000000) (610685290114440384681343/1000000000000000000000000) (1495869095321283/200000000000000000000000) where
  r0 := (611461149861/1000000000000000000)
  k0 := (1848388264096139/500000000000000000)
  k6 := (1162225122680597/100000000000000000)
  q := (166619326610090463419/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13881]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13881]

theorem width_13882 : mW 13882 = 315197047137044 := by
  have hu : mW 13882 ≤ 315197047137044 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13882 ≤ 315197047137043 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13882 : RowArithmetic 13882 (35236812019667513673/31250000000000000000000) (24426948905192058875883/40000000000000000000000) (186948552893413/25000000000000000000000) where
  r0 := (152848770119/250000000000000000)
  k0 := (46207210017483/12500000000000000)
  k6 := (1452729076324117/125000000000000000)
  q := (166625328206728523161/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13882]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13882]

theorem width_13883 : mW 13883 = 315276523365606 := by
  have hu : mW 13883 ≤ 315276523365606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13883 ≤ 315276523365605 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13883 : RowArithmetic 13883 (563772821078581898271/500000000000000000000000) (122132431362475112451419/200000000000000000000000) (3738269561439259/500000000000000000000000) where
  r0 := (152832255747/250000000000000000)
  k0 := (1848188549890257/500000000000000000)
  k6 := (2324282807922089/200000000000000000)
  q := (166631329587205778859/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13883]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13883]

theorem width_13884 : mW 13884 = 315356013907246 := by
  have hu : mW 13884 ≤ 315356013907246 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13884 ≤ 315356013907245 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13884 : RowArithmetic 13884 (1127513307491256682981/1000000000000000000000000) (610650592661778794608593/1000000000000000000000000) (934392062238567/125000000000000000000000) where
  r0 := (305631488697/500000000000000000)
  k0 := (3696177423332909/1000000000000000000)
  k6 := (726312219615647/62500000000000000)
  q := (2082966634394319817/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13884]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13884]

theorem width_13885 : mW 13885 = 315435518763511 := by
  have hu : mW 13885 ≤ 315435518763511 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13885 ≤ 315435518763510 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13885 : RowArithmetic 13885 (1127480980629172642647/1000000000000000000000000) (152659757544406855357927/250000000000000000000000) (7473734240702731/1000000000000000000000000) where
  r0 := (152799235923/250000000000000000)
  k0 := (3695977772053859/1000000000000000000)
  k6 := (2324115406660903/200000000000000000)
  q := (166643331699771293309/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13885]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13885]

theorem width_13886 : mW 13886 = 315515037935947 := by
  have hu : mW 13886 ≤ 315515037935947 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13886 ≤ 315515037935946 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13886 : RowArithmetic 13886 (56372433078422341619/50000000000000000000000) (610627469359537861099501/1000000000000000000000000) (3736166175568667/500000000000000000000000) where
  r0 := (305565460939/500000000000000000)
  k0 := (1847889072967673/500000000000000000)
  k6 := (5810079298982397/500000000000000000)
  q := (83324666215953124573/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13886]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13886]

theorem width_13887 : mW 13887 = 315594571426100 := by
  have hu : mW 13887 ≤ 315594571426100 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13887 ≤ 315594571426099 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13887 : RowArithmetic 13887 (1127416350306615404559/1000000000000000000000000) (24424636408285064067067/40000000000000000000000) (7470930829088627/1000000000000000000000000) where
  r0 := (611064911949/1000000000000000000)
  k0 := (3695578544972377/1000000000000000000)
  k6 := (11619740207823049/1000000000000000000)
  q := (83327666473986897553/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13887]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13887]

theorem width_13888 : mW 13888 = 315674119235518 := by
  have hu : mW 13888 ≤ 315674119235518 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13888 ≤ 315674119235517 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13888 : RowArithmetic 13888 (1127384046841214279709/1000000000000000000000000) (152651088180002559425173/250000000000000000000000) (7469529674432899/1000000000000000000000000) where
  r0 := (610998913903/1000000000000000000)
  k0 := (3695378969162981/1000000000000000000)
  k6 := (5809660931435573/500000000000000000)
  q := (6666453329919890769/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13888]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13888]

theorem width_13889 : mW 13889 = 315753681365746 := by
  have hu : mW 13889 ≤ 315753681365746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13889 ≤ 315753681365745 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13889 : RowArithmetic 13889 (1127351751169782214453/1000000000000000000000000) (15264819922445140004001/25000000000000000000000) (7468128887046561/1000000000000000000000000) where
  r0 := (76366615967/125000000000000000)
  k0 := (739035883699827/200000000000000000)
  k6 := (232378071262019/20000000000000000)
  q := (83333666666000002667/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13889]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13889]

theorem width_13890 : mW 13890 = 315833257818333 := by
  have hu : mW 13890 ≤ 315833257818333 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13890 ≤ 315833257818332 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13890 : RowArithmetic 13890 (1127319463289856506679/1000000000000000000000000) (61058124274012947897569/100000000000000000000000) (7466728466805983/1000000000000000000000000) where
  r0 := (122173390689/200000000000000000)
  k0 := (23093624331099/6250000000000000)
  k6 := (11618485308504327/1000000000000000000)
  q := (166673333200005333067/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13890]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13890]

theorem width_13891 : mW 13891 = 315912848594824 := by
  have hu : mW 13891 ≤ 315912848594824 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13891 ≤ 315912848594823 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13891 : RowArithmetic 13891 (563643591599488950743/500000000000000000000000) (610569690246598901806527/1000000000000000000000000) (7465328413587679/1000000000000000000000000) where
  r0 := (152700247757/250000000000000000)
  k0 := (1847390196295561/500000000000000000)
  k6 := (232361341981463/20000000000000000)
  q := (166679332852036577859/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13891]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13891]

theorem width_13892 : mW 13892 = 315992453696767 := by
  have hu : mW 13892 ≤ 315992453696767 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13892 ≤ 315992453696766 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13892 : RowArithmetic 13892 (140906863861835787333/125000000000000000000000) (610558139416830954347291/1000000000000000000000000) (3731964363634073/500000000000000000000000) where
  r0 := (610735040481/1000000000000000000)
  k0 := (461822614667119/125000000000000000)
  k6 := (1452206116849911/125000000000000000)
  q := (83342666144058530473/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13892]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13892]

theorem width_13893 : mW 13893 = 316072073125708 := by
  have hu : mW 13893 ≤ 316072073125708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13893 ≤ 316072073125707 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13893 : RowArithmetic 13893 (1127222646374523816791/1000000000000000000000000) (610546590250442909838029/1000000000000000000000000) (7462529407723981/1000000000000000000000000) where
  r0 := (610669101801/1000000000000000000)
  k0 := (3694381467208327/1000000000000000000)
  k6 := (1452153851959327/125000000000000000)
  q := (166691331508270099367/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13893]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13893]

theorem width_13894 : mW 13894 = 316151706883195 := by
  have hu : mW 13894 ≤ 316151706883195 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13894 ≤ 316151706883194 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13894 : RowArithmetic 13894 (1127190389636032342561/1000000000000000000000000) (610535042747052087161563/1000000000000000000000000) (7461130454831783/1000000000000000000000000) where
  r0 := (305301587493/500000000000000000)
  k0 := (3694182042203267/1000000000000000000)
  k6 := (11616812741691011/1000000000000000000)
  q := (83348665256259502983/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13894]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13894]

theorem width_13895 : mW 13895 = 316231354970774 := by
  have hu : mW 13895 ≤ 316231354970774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13895 ≤ 316231354970773 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13895 : RowArithmetic 13895 (281789535169188994849/250000000000000000000000) (152630874226568993588923/250000000000000000000000) (1864932967117063/250000000000000000000000) where
  r0 := (596227793/976562500000000)
  k0 := (184699132115687/50000000000000000)
  k6 := (232327894256807/20000000000000000)
  q := (10418958081305443087/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13895]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13895]

theorem width_13896 : mW 13896 = 316311017389993 := by
  have hu : mW 13896 ≤ 316311017389993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13896 ≤ 316311017389992 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13896 : RowArithmetic 13896 (563562949747119299413/500000000000000000000000) (122102390545546425573571/200000000000000000000000) (7458333648510093/1000000000000000000000000) where
  r0 := (610471356937/1000000000000000000)
  k0 := (3693783267537763/1000000000000000000)
  k6 := (11615976729114513/1000000000000000000)
  q := (83354663936698827051/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13896]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13896]

theorem width_13897 : mW 13897 = 316390694142399 := by
  have hu : mW 13897 ≤ 316390694142399 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13897 ≤ 316390694142398 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13897 : RowArithmetic 13897 (1127093666086025675917/1000000000000000000000000) (610500410211038317951969/1000000000000000000000000) (3728467897417043/500000000000000000000000) where
  r0 := (610405465697/1000000000000000000)
  k0 := (36935839178673/10000000000000000)
  k6 := (5807779395252691/500000000000000000)
  q := (166715326230074000357/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13897]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13897]

theorem width_13898 : mW 13898 = 316470385229539 := by
  have hu : mW 13898 ≤ 316470385229539 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13898 ≤ 316470385229538 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13898 : RowArithmetic 13898 (225412288089932735321/200000000000000000000000) (152622217338953089538447/250000000000000000000000) (7455538307317063/1000000000000000000000000) where
  r0 := (610339586309/1000000000000000000)
  k0 := (3693384593297339/1000000000000000000)
  k6 := (5807570448502421/500000000000000000)
  q := (166721324370939424229/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13898]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13898]

theorem width_13899 : mW 13899 = 316550090652960 := by
  have hu : mW 13899 ≤ 316550090652960 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13899 ≤ 316550090652959 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13899 : RowArithmetic 13899 (1127029222582700057173/1000000000000000000000000) (305238665080836106797843/500000000000000000000000) (1863535296458977/250000000000000000000000) where
  r0 := (610273718771/1000000000000000000)
  k0 := (1846592646912947/500000000000000000)
  k6 := (5807361524302389/500000000000000000)
  q := (104204576435010761/625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13899]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13899]

theorem width_13900 : mW 13900 = 316629810414209 := by
  have hu : mW 13900 ≤ 316629810414209 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13900 ≤ 316629810414208 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13900 : RowArithmetic 13900 (563498506241341631871/500000000000000000000000) (152616448157058983183207/250000000000000000000000) (1863186107566889/250000000000000000000000) where
  r0 := (15255196577/25000000000000000)
  k0 := (3692986019447949/1000000000000000000)
  k6 := (290357631132427/25000000000000000)
  q := (260520812508329169/1562500000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13900]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13900]

theorem width_13901 : mW 13901 = 316709544514835 := by
  have hu : mW 13901 ≤ 316709544514835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13901 ≤ 316709544514834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13901 : RowArithmetic 13901 (1126964810147161511547/1000000000000000000000000) (610454256755121696102337/1000000000000000000000000) (7451348040488947/1000000000000000000000000) where
  r0 := (610142019231/1000000000000000000)
  k0 := (738557354030487/200000000000000000)
  k6 := (11613887487073637/1000000000000000000)
  q := (41684829374725764853/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13901]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13901]

theorem width_13902 : mW 13902 = 316789292956384 := by
  have hu : mW 13902 ≤ 316789292956384 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13902 ≤ 316789292956383 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13902 : RowArithmetic 13902 (281733153893421459053/250000000000000000000000) (12208854450838958016419/20000000000000000000000) (1489990403275429/200000000000000000000000) where
  r0 := (76259523403/125000000000000000)
  k0 := (1846293772971707/500000000000000000)
  k6 := (11613469773926341/1000000000000000000)
  q := (83372657388378835337/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13902]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13902]

theorem width_13903 : mW 13903 = 316869055740405 := by
  have hu : mW 13903 ≤ 316869055740405 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13903 ≤ 316869055740404 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13903 : RowArithmetic 13903 (281725107189951607963/250000000000000000000000) (24417247599533316641617/40000000000000000000000) (7448556357809193/1000000000000000000000000) where
  r0 := (305005183527/500000000000000000)
  k0 := (3692388346809813/1000000000000000000)
  k6 := (725815756615443/62500000000000000)
  q := (166751311838917777073/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13903]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13903]

theorem width_13904 : mW 13904 = 316948832868443 := by
  have hu : mW 13904 ≤ 316948832868443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13904 ≤ 316948832868442 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13904 : RowArithmetic 13904 (56343412485153845987/50000000000000000000000) (610419659093895277929421/1000000000000000000000000) (186179026616557/25000000000000000000000) where
  r0 := (304972279359/500000000000000000)
  k0 := (3692189172746611/1000000000000000000)
  k6 := (11612634482827773/1000000000000000000)
  q := (41689327171351662389/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13904]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13904]

theorem width_13905 : mW 13905 = 317028624342048 := by
  have hu : mW 13905 ≤ 317028624342048 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13905 ≤ 317028624342047 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13905 : RowArithmetic 13905 (563418039200524430483/500000000000000000000000) (76301016232281719232787/125000000000000000000000) (1861441534203383/250000000000000000000000) where
  r0 := (304939381107/500000000000000000)
  k0 := (922997505937953/250000000000000000)
  k6 := (2322443380972059/200000000000000000)
  q := (166763305316247554881/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13905]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13905]

theorem width_13906 : mW 13906 = 317108430162767 := by
  have hu : mW 13906 ≤ 317108430162767 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13906 ≤ 317108430162766 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13906 : RowArithmetic 13906 (1126803914851276632899/1000000000000000000000000) (122079320456205409841831/200000000000000000000000) (7444371574140193/1000000000000000000000000) where
  r0 := (609812977539/1000000000000000000)
  k0 := (3691790899820391/1000000000000000000)
  k6 := (5805899685968277/500000000000000000)
  q := (83384650865731877813/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13906]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13906]

theorem width_13907 : mW 13907 = 317188250332147 := by
  have hu : mW 13907 ≤ 317188250332147 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13907 ≤ 317188250332146 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13907 : RowArithmetic 13907 (1126771759051315599137/1000000000000000000000000) (305192538180917078772033/500000000000000000000000) (3721488688259781/500000000000000000000000) where
  r0 := (609747204689/1000000000000000000)
  k0 := (461448975118037/125000000000000000)
  k6 := (11611381884048453/1000000000000000000)
  q := (83387648965539255093/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13907]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13907]

theorem width_13908 : mW 13908 = 317268084851736 := by
  have hu : mW 13908 ≤ 317268084851736 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13908 ≤ 317268084851735 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13908 : RowArithmetic 13908 (28168490274968037517/25000000000000000000000) (610373552100294040938981/1000000000000000000000000) (1488316708765793/200000000000000000000000) where
  r0 := (304840721831/500000000000000000)
  k0 := (3691392727121527/1000000000000000000)
  k6 := (11610964441187897/1000000000000000000)
  q := (20847661739389384097/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13908]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13908]

theorem width_13909 : mW 13909 = 317347933723083 := by
  have hu : mW 13909 ≤ 317347933723083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13909 ≤ 317347933723082 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13909 : RowArithmetic 13909 (1126707470691050456689/1000000000000000000000000) (305181014748012961220359/500000000000000000000000) (1488038015189151/200000000000000000000000) where
  r0 := (304807847227/500000000000000000)
  k0 := (1845596839172013/500000000000000000)
  k6 := (1451318380418349/125000000000000000)
  q := (166787289683596693429/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13909]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13909]

theorem width_13910 : mW 13910 = 317427796947735 := by
  have hu : mW 13910 ≤ 317427796947735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13910 ≤ 317427796947734 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13910 : RowArithmetic 13910 (563337669062930394331/500000000000000000000000) (61035050854864902699631/100000000000000000000000) (1487759394549477/200000000000000000000000) where
  r0 := (609549957063/1000000000000000000)
  k0 := (3690994654609791/1000000000000000000)
  k6 := (11610129690517047/1000000000000000000)
  q := (166793285236546618001/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13910]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13910]

theorem width_13911 : mW 13911 = 317507674527239 := by
  have hu : mW 13911 ≤ 317507674527239 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13911 ≤ 317507674527238 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13911 : RowArithmetic 13911 (35207600415647243821/31250000000000000000000) (122067797851556558566119/200000000000000000000000) (7437404234111359/1000000000000000000000000) where
  r0 := (304742115743/500000000000000000)
  k0 := (369079565591379/100000000000000000)
  k6 := (2902428095672643/250000000000000000)
  q := (16679928057398808817/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13911]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13911]

theorem width_13912 : mW 13912 = 317587566463145 := by
  have hu : mW 13912 ≤ 317587566463145 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13912 ≤ 317587566463144 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13912 : RowArithmetic 13912 (1126611096213161964967/1000000000000000000000000) (610327471623046744012407/1000000000000000000000000) (7436011859915163/1000000000000000000000000) where
  r0 := (15235462943/25000000000000000)
  k0 := (922649170562747/250000000000000000)
  k6 := (11609295119859281/1000000000000000000)
  q := (41701318923986085359/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13912]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13912]

theorem width_13913 : mW 13913 = 317667472756999 := by
  have hu : mW 13913 ≤ 317667472756999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13913 ≤ 317667472756998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13913 : RowArithmetic 13913 (225315797372154631713/200000000000000000000000) (610315955644060471681447/1000000000000000000000000) (7434619850036427/1000000000000000000000000) where
  r0 := (609352815761/1000000000000000000)
  k0 := (3690397733613323/1000000000000000000)
  k6 := (11608877902015087/1000000000000000000)
  q := (41702817650609652781/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13913]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13913]

theorem width_13914 : mW 13914 = 317747393410351 := by
  have hu : mW 13914 ≤ 317747393410351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13914 ≤ 317747393410350 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13914 : RowArithmetic 13914 (1126546885241105819357/1000000000000000000000000) (610304441320443753401863/1000000000000000000000000) (7433228204352739/1000000000000000000000000) where
  r0 := (609287125607/1000000000000000000)
  k0 := (1845099404999393/500000000000000000)
  k6 := (2902115182287477/250000000000000000)
  q := (10426079080843382899/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13914]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13914]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13840 then ⟨(1128943450346675729891/1000000000000000000000000), (24446439888348531820729/40000000000000000000000), (3768600833154149/500000000000000000000000)⟩ else
  if n = 13841 then ⟨(1128910777770578274917/1000000000000000000000000), (611149361036338842166841/1000000000000000000000000), (1883945777413779/250000000000000000000000)⟩ else
  if n = 13842 then ⟨(564439056552611542071/500000000000000000000000), (611137726547020425315551/1000000000000000000000000), (7534364926137179/1000000000000000000000000)⟩ else
  if n = 13843 then ⟨(70552841021756494291/62500000000000000000000), (611126093740369218722813/1000000000000000000000000), (301317884625141/40000000000000000000000)⟩ else
  if n = 13844 then ⟨(564406403748357132393/500000000000000000000000), (61111446261599638981739/100000000000000000000000), (3765764839001597/500000000000000000000000)⟩ else
  if n = 13845 then ⟨(1128780166548548685443/1000000000000000000000000), (611102833173513418776047/1000000000000000000000000), (94126407664191/12500000000000000000000)⟩ else
  if n = 13846 then ⟨(28218688337527614817/25000000000000000000000), (305545602706265887393601/500000000000000000000000), (7528695920899003/1000000000000000000000000)⟩ else
  if n = 13847 then ⟨(1128714908351877300417/1000000000000000000000000), (611079579332663046536507/1000000000000000000000000), (7527279601168517/1000000000000000000000000)⟩ else
  if n = 13848 then ⟨(141085286387295704377/125000000000000000000000), (305533977466759502527451/500000000000000000000000), (7525863653818123/1000000000000000000000000)⟩ else
  if n = 13849 then ⟨(1128649681738068811623/1000000000000000000000000), (9547755190854868663241/15625000000000000000000), (7524448078722153/1000000000000000000000000)⟩ else
  if n = 13850 then ⟨(225723416053697162327/200000000000000000000000), (305522355587926347727243/500000000000000000000000), (7523032875754943/1000000000000000000000000)⟩ else
  if n = 13851 then ⟨(1128584486687117877001/1000000000000000000000000), (305516545908277231001633/500000000000000000000000), (7521618044790929/1000000000000000000000000)⟩ else
  if n = 13852 then ⟨(1128551900991466638697/1000000000000000000000000), (7637768426705364904141/12500000000000000000000), (7520203585704579/1000000000000000000000000)⟩ else
  if n = 13853 then ⟨(282129830794758996273/250000000000000000000000), (611009858135089173548309/1000000000000000000000000), (375939474918523/50000000000000000000000)⟩ else
  if n = 13854 then ⟨(564243376623664162603/500000000000000000000000), (610998243812146961107581/1000000000000000000000000), (7517375782663097/1000000000000000000000000)⟩ else
  if n = 13855 then ⟨(225690838238769789489/200000000000000000000000), (305493315583607529765419/500000000000000000000000), (7515962438457139/1000000000000000000000000)⟩ else
  if n = 13856 then ⟨(564210818508052074959/500000000000000000000000), (76371877524988288928463/125000000000000000000000), (939318683203411/125000000000000000000000)⟩ else
  if n = 13857 then ⟨(282097272677899999237/250000000000000000000000), (610963410909833522796029/1000000000000000000000000), (7513136864048251/1000000000000000000000000)⟩ else
  if n = 13858 then ⟨(70522284517365261551/62500000000000000000000), (305475901648304831481449/500000000000000000000000), (3755862316797407/500000000000000000000000)⟩ else
  if n = 13859 then ⟨(564162010856173019963/500000000000000000000000), (76367524669980983667823/125000000000000000000000), (1877578193535459/250000000000000000000000)⟩ else
  if n = 13860 then ⟨(282072874753153508547/250000000000000000000000), (152732148274790332198749/250000000000000000000000), (7508901285564161/1000000000000000000000000)⟩ else
  if n = 13861 then ⟨(1128258984176160131449/1000000000000000000000000), (61091699051416337033793/100000000000000000000000), (3753745083868389/500000000000000000000000)⟩ else
  if n = 13862 then ⟨(112822647720049544053/100000000000000000000000), (305452694802233732225337/500000000000000000000000), (7506079420534659/1000000000000000000000000)⟩ else
  if n = 13863 then ⟨(70512123630195754897/62500000000000000000000), (305446895184843634216817/500000000000000000000000), (750466904383283/100000000000000000000000)⟩ else
  if n = 13864 then ⟨(1128161486821583789063/1000000000000000000000000), (610882192809436361751347/1000000000000000000000000), (750325903750639/100000000000000000000000)⟩ else
  if n = 13865 then ⟨(564064501706682661407/500000000000000000000000), (610870596923328720511311/1000000000000000000000000), (3750924700715247/500000000000000000000000)⟩ else
  if n = 13866 then ⟨(11280965278559918161/10000000000000000000000), (610859002710978188657639/1000000000000000000000000), (300017605419213/40000000000000000000000)⟩ else
  if n = 13867 then ⟨(1128064060146980649159/1000000000000000000000000), (152711852542999729865027/250000000000000000000000), (1499806247906233/200000000000000000000000)⟩ else
  if n = 13868 then ⟨(1128031600283847731163/1000000000000000000000000), (610835819306005057733587/1000000000000000000000000), (3748811356729127/500000000000000000000000)⟩ else
  if n = 13869 then ⟨(140999893533014133759/125000000000000000000000), (610824230112610927729681/1000000000000000000000000), (3748107278568503/500000000000000000000000)⟩ else
  if n = 13870 then ⟨(1127966704085294584681/1000000000000000000000000), (610812642591431019755289/1000000000000000000000000), (1498961354088553/200000000000000000000000)⟩ else
  if n = 13871 then ⟨(70495891734057104443/62500000000000000000000), (610801056742079841003967/1000000000000000000000000), (299735974130041/40000000000000000000000)⟩ else
  if n = 13872 then ⟨(563950919620245436981/500000000000000000000000), (152697368141043018357319/250000000000000000000000), (374599615271863/50000000000000000000000)⟩ else
  if n = 13873 then ⟨(281967354642387244121/250000000000000000000000), (610777890057322585283683/1000000000000000000000000), (1872646406719261/250000000000000000000000)⟩ else
  if n = 13874 then ⟨(1127837005729611146063/1000000000000000000000000), (610766309221146256187629/1000000000000000000000000), (7489179317445983/1000000000000000000000000)⟩ else
  if n = 13875 then ⟨(225560920143640310381/200000000000000000000000), (610754730055258153345413/1000000000000000000000000), (748777337701973/100000000000000000000000)⟩ else
  if n = 13876 then ⟨(1127772203532845364491/1000000000000000000000000), (122148630511854691385429/200000000000000000000000), (1497273561094799/200000000000000000000000)⟩ else
  if n = 13877 then ⟨(1127739814171068755053/1000000000000000000000000), (15268289418320185837211/25000000000000000000000), (7484962602684537/1000000000000000000000000)⟩ else
  if n = 13878 then ⟨(281926858157599723763/250000000000000000000000), (305360001287737748510231/500000000000000000000000), (7483557768527171/1000000000000000000000000)⟩ else
  if n = 13879 then ⟨(140959382363545417487/125000000000000000000000), (305354215043446617646313/500000000000000000000000), (7482153302877737/1000000000000000000000000)⟩ else
  if n = 13880 then ⟨(140955336625311407589/125000000000000000000000), (610696859266676286287163/1000000000000000000000000), (3740374602806077/500000000000000000000000)⟩ else
  if n = 13881 then ⟨(225522066982062688507/200000000000000000000000), (610685290114440384681343/1000000000000000000000000), (1495869095321283/200000000000000000000000)⟩ else
  if n = 13882 then ⟨(35236812019667513673/31250000000000000000000), (24426948905192058875883/40000000000000000000000), (186948552893413/25000000000000000000000)⟩ else
  if n = 13883 then ⟨(563772821078581898271/500000000000000000000000), (122132431362475112451419/200000000000000000000000), (3738269561439259/500000000000000000000000)⟩ else
  if n = 13884 then ⟨(1127513307491256682981/1000000000000000000000000), (610650592661778794608593/1000000000000000000000000), (934392062238567/125000000000000000000000)⟩ else
  if n = 13885 then ⟨(1127480980629172642647/1000000000000000000000000), (152659757544406855357927/250000000000000000000000), (7473734240702731/1000000000000000000000000)⟩ else
  if n = 13886 then ⟨(56372433078422341619/50000000000000000000000), (610627469359537861099501/1000000000000000000000000), (3736166175568667/500000000000000000000000)⟩ else
  if n = 13887 then ⟨(1127416350306615404559/1000000000000000000000000), (24424636408285064067067/40000000000000000000000), (7470930829088627/1000000000000000000000000)⟩ else
  if n = 13888 then ⟨(1127384046841214279709/1000000000000000000000000), (152651088180002559425173/250000000000000000000000), (7469529674432899/1000000000000000000000000)⟩ else
  if n = 13889 then ⟨(1127351751169782214453/1000000000000000000000000), (15264819922445140004001/25000000000000000000000), (7468128887046561/1000000000000000000000000)⟩ else
  if n = 13890 then ⟨(1127319463289856506679/1000000000000000000000000), (61058124274012947897569/100000000000000000000000), (7466728466805983/1000000000000000000000000)⟩ else
  if n = 13891 then ⟨(563643591599488950743/500000000000000000000000), (610569690246598901806527/1000000000000000000000000), (7465328413587679/1000000000000000000000000)⟩ else
  if n = 13892 then ⟨(140906863861835787333/125000000000000000000000), (610558139416830954347291/1000000000000000000000000), (3731964363634073/500000000000000000000000)⟩ else
  if n = 13893 then ⟨(1127222646374523816791/1000000000000000000000000), (610546590250442909838029/1000000000000000000000000), (7462529407723981/1000000000000000000000000)⟩ else
  if n = 13894 then ⟨(1127190389636032342561/1000000000000000000000000), (610535042747052087161563/1000000000000000000000000), (7461130454831783/1000000000000000000000000)⟩ else
  if n = 13895 then ⟨(281789535169188994849/250000000000000000000000), (152630874226568993588923/250000000000000000000000), (1864932967117063/250000000000000000000000)⟩ else
  if n = 13896 then ⟨(563562949747119299413/500000000000000000000000), (122102390545546425573571/200000000000000000000000), (7458333648510093/1000000000000000000000000)⟩ else
  if n = 13897 then ⟨(1127093666086025675917/1000000000000000000000000), (610500410211038317951969/1000000000000000000000000), (3728467897417043/500000000000000000000000)⟩ else
  if n = 13898 then ⟨(225412288089932735321/200000000000000000000000), (152622217338953089538447/250000000000000000000000), (7455538307317063/1000000000000000000000000)⟩ else
  if n = 13899 then ⟨(1127029222582700057173/1000000000000000000000000), (305238665080836106797843/500000000000000000000000), (1863535296458977/250000000000000000000000)⟩ else
  if n = 13900 then ⟨(563498506241341631871/500000000000000000000000), (152616448157058983183207/250000000000000000000000), (1863186107566889/250000000000000000000000)⟩ else
  if n = 13901 then ⟨(1126964810147161511547/1000000000000000000000000), (610454256755121696102337/1000000000000000000000000), (7451348040488947/1000000000000000000000000)⟩ else
  if n = 13902 then ⟨(281733153893421459053/250000000000000000000000), (12208854450838958016419/20000000000000000000000), (1489990403275429/200000000000000000000000)⟩ else
  if n = 13903 then ⟨(281725107189951607963/250000000000000000000000), (24417247599533316641617/40000000000000000000000), (7448556357809193/1000000000000000000000000)⟩ else
  if n = 13904 then ⟨(56343412485153845987/50000000000000000000000), (610419659093895277929421/1000000000000000000000000), (186179026616557/25000000000000000000000)⟩ else
  if n = 13905 then ⟨(563418039200524430483/500000000000000000000000), (76301016232281719232787/125000000000000000000000), (1861441534203383/250000000000000000000000)⟩ else
  if n = 13906 then ⟨(1126803914851276632899/1000000000000000000000000), (122079320456205409841831/200000000000000000000000), (7444371574140193/1000000000000000000000000)⟩ else
  if n = 13907 then ⟨(1126771759051315599137/1000000000000000000000000), (305192538180917078772033/500000000000000000000000), (3721488688259781/500000000000000000000000)⟩ else
  if n = 13908 then ⟨(28168490274968037517/25000000000000000000000), (610373552100294040938981/1000000000000000000000000), (1488316708765793/200000000000000000000000)⟩ else
  if n = 13909 then ⟨(1126707470691050456689/1000000000000000000000000), (305181014748012961220359/500000000000000000000000), (1488038015189151/200000000000000000000000)⟩ else
  if n = 13910 then ⟨(563337669062930394331/500000000000000000000000), (61035050854864902699631/100000000000000000000000), (1487759394549477/200000000000000000000000)⟩ else
  if n = 13911 then ⟨(35207600415647243821/31250000000000000000000), (122067797851556558566119/200000000000000000000000), (7437404234111359/1000000000000000000000000)⟩ else
  if n = 13912 then ⟨(1126611096213161964967/1000000000000000000000000), (610327471623046744012407/1000000000000000000000000), (7436011859915163/1000000000000000000000000)⟩ else
  if n = 13913 then ⟨(225315797372154631713/200000000000000000000000), (610315955644060471681447/1000000000000000000000000), (7434619850036427/1000000000000000000000000)⟩ else
  ⟨(1126546885241105819357/1000000000000000000000000), (610304441320443753401863/1000000000000000000000000), (7433228204352739/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13840 ≤ n) (hb : n ≤ 13914) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13840
  · exact row_13841
  · exact row_13842
  · exact row_13843
  · exact row_13844
  · exact row_13845
  · exact row_13846
  · exact row_13847
  · exact row_13848
  · exact row_13849
  · exact row_13850
  · exact row_13851
  · exact row_13852
  · exact row_13853
  · exact row_13854
  · exact row_13855
  · exact row_13856
  · exact row_13857
  · exact row_13858
  · exact row_13859
  · exact row_13860
  · exact row_13861
  · exact row_13862
  · exact row_13863
  · exact row_13864
  · exact row_13865
  · exact row_13866
  · exact row_13867
  · exact row_13868
  · exact row_13869
  · exact row_13870
  · exact row_13871
  · exact row_13872
  · exact row_13873
  · exact row_13874
  · exact row_13875
  · exact row_13876
  · exact row_13877
  · exact row_13878
  · exact row_13879
  · exact row_13880
  · exact row_13881
  · exact row_13882
  · exact row_13883
  · exact row_13884
  · exact row_13885
  · exact row_13886
  · exact row_13887
  · exact row_13888
  · exact row_13889
  · exact row_13890
  · exact row_13891
  · exact row_13892
  · exact row_13893
  · exact row_13894
  · exact row_13895
  · exact row_13896
  · exact row_13897
  · exact row_13898
  · exact row_13899
  · exact row_13900
  · exact row_13901
  · exact row_13902
  · exact row_13903
  · exact row_13904
  · exact row_13905
  · exact row_13906
  · exact row_13907
  · exact row_13908
  · exact row_13909
  · exact row_13910
  · exact row_13911
  · exact row_13912
  · exact row_13913
  · exact row_13914

end BstLean.Part271.R3.Rows13840
