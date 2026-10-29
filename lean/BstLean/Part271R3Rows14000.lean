import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14000–14074. -/
namespace BstLean.Part271.R3.Rows14000
open Real BstLean.Part130 BstLean.Part227

theorem width_14000 : mW 14000 = 324674458496507 := by
  have hu : mW 14000 ≤ 324674458496507 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14000 ≤ 324674458496506 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14000 : RowArithmetic 14000 (280953702195227367387/250000000000000000000000) (304660180395427831229887/500000000000000000000000) (58519166581423/8000000000000000000000) where
  r0 := (603681610521/1000000000000000000)
  k0 := (3673184448832423/1000000000000000000)
  k6 := (5786375623578447/500000000000000000)
  q := (41833001326703777399/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14000]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14000]

theorem width_14001 : mW 14001 = 324755634358588 := by
  have hu : mW 14001 ≤ 324755634358588 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14001 ≤ 324755634358587 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14001 : RowArithmetic 14001 (561891685340282029781/500000000000000000000000) (121861797808459626203853/200000000000000000000000) (7313535399180661/1000000000000000000000000) where
  r0 := (603616936123/1000000000000000000)
  k0 := (1836493841695981/500000000000000000)
  k6 := (5786168978376389/500000000000000000)
  q := (167337981343148752591/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14001]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14001]

theorem width_14002 : mW 14002 = 324836824716617 := by
  have hu : mW 14002 ≤ 324836824716617 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14002 ≤ 324836824716616 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14002 : RowArithmetic 14002 (561875970051014582951/500000000000000000000000) (609297618916112179350469/1000000000000000000000000) (228505479040747/31250000000000000000000) where
  r0 := (75444034159/125000000000000000)
  k0 := (73455818850869/20000000000000000)
  k6 := (11571924710624243/1000000000000000000)
  q := (8367197858303579043/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14002]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14002]

theorem width_14003 : mW 14003 = 324918029572148 := by
  have hu : mW 14003 ≤ 324918029572148 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14003 ≤ 324918029572147 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14003 : RowArithmetic 14003 (1123720517042948628367/1000000000000000000000000) (609286250411927995819799/1000000000000000000000000) (1827703903232397/250000000000000000000000) where
  r0 := (120697524393/200000000000000000)
  k0 := (367259422628171/100000000000000000)
  k6 := (11571511508763383/1000000000000000000)
  q := (167349932775606456173/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14003]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14003]

theorem width_14004 : mW 14004 = 324999248926733 := by
  have hu : mW 14004 ≤ 324999248926733 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14004 ≤ 324999248926732 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14004 : RowArithmetic 14004 (561844550750484200079/500000000000000000000000) (152318720882343989473923/250000000000000000000000) (7309456249939787/1000000000000000000000000) where
  r0 := (3017114911/5000000000000000)
  k0 := (57381211478197/15625000000000000)
  k6 := (2314219670232459/200000000000000000)
  q := (167355908171776236219/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14004]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14004]

theorem width_14005 : mW 14005 = 325080482781926 := by
  have hu : mW 14005 ≤ 325080482781926 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14005 ≤ 325080482781925 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14005 : RowArithmetic 14005 (112365769347373420829/100000000000000000000000) (609263518268086507201429/1000000000000000000000000) (913512155027073/125000000000000000000000) where
  r0 := (603358353973/1000000000000000000)
  k0 := (1836100433751961/500000000000000000)
  k6 := (289267130945327/25000000000000000)
  q := (167361883354603774607/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14005]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14005]

theorem width_14006 : mW 14006 = 325161731139281 := by
  have hu : mW 14006 ≤ 325161731139281 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14006 ≤ 325161731139280 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14006 : RowArithmetic 14006 (140453286619861590423/125000000000000000000000) (304626077313845116967523/500000000000000000000000) (7306738583642109/1000000000000000000000000) where
  r0 := (301646868641/500000000000000000)
  k0 := (3672004224977513/1000000000000000000)
  k6 := (11570272168707837/1000000000000000000)
  q := (83683929162055960433/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14006]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14006]

theorem width_14007 : mW 14007 = 325242994000349 := by
  have hu : mW 14007 ≤ 325242994000349 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14007 ≤ 325242994000348 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14007 : RowArithmetic 14007 (561797449977046655109/500000000000000000000000) (60924079260781783232189/100000000000000000000000) (7305380280098607/1000000000000000000000000) where
  r0 := (150807283031/250000000000000000)
  k0 := (3671807607020199/1000000000000000000)
  k6 := (11569859143838671/1000000000000000000)
  q := (33474766616064704089/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14007]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14007]

theorem width_14008 : mW 14008 = 325324271366685 := by
  have hu : mW 14008 ≤ 325324271366685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14008 ≤ 325324271366684 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14008 : RowArithmetic 14008 (224712702891396787907/200000000000000000000000) (609229432208100012178691/1000000000000000000000000) (1460804465893657/200000000000000000000000) where
  r0 := (120632907699/200000000000000000)
  k0 := (1835805506811877/500000000000000000)
  k6 := (5784723081598843/500000000000000000)
  q := (167379807623261414717/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14008]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14008]

theorem width_14009 : mW 14009 = 325405563239842 := by
  have hu : mW 14009 ≤ 325405563239842 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14009 ≤ 325405563239841 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14009 : RowArithmetic 14009 (1123532136465214691581/1000000000000000000000000) (152304518357041963409523/250000000000000000000000) (3651332365816721/500000000000000000000000) where
  r0 := (301549978197/500000000000000000)
  k0 := (3671414444789079/1000000000000000000)
  k6 := (11569033226776989/1000000000000000000)
  q := (167385781952948440979/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14009]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14009]

theorem width_14010 : mW 14010 = 325486869621374 := by
  have hu : mW 14010 ≤ 325486869621374 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14010 ≤ 325486869621373 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14010 : RowArithmetic 14010 (280875191494109001083/250000000000000000000000) (609206716267652277757869/1000000000000000000000000) (7301307486476407/1000000000000000000000000) where
  r0 := (75379423227/125000000000000000)
  k0 := (36712179005049/10000000000000000)
  k6 := (11568620334568689/1000000000000000000)
  q := (41847939017351858113/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14010]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14010]

theorem width_14011 : mW 14011 = 325568190512833 := by
  have hu : mW 14011 ≤ 325568190512833 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14011 ≤ 325568190512832 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14011 : RowArithmetic 14011 (561734701494150211177/500000000000000000000000) (609195360726184485517929/1000000000000000000000000) (7299950593879599/1000000000000000000000000) where
  r0 := (15074270669/25000000000000000)
  k0 := (734204276154423/200000000000000000)
  k6 := (11568207486564897/1000000000000000000)
  q := (41849432493165304571/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14011]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14011]

theorem width_14012 : mW 14012 = 325649525915774 := by
  have hu : mW 14012 ≤ 325649525915774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14012 ≤ 325649525915773 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14012 : RowArithmetic 14012 (280859511874614920387/250000000000000000000000) (152296001700848917826437/250000000000000000000000) (3649297026862711/500000000000000000000000) where
  r0 := (301453139611/500000000000000000)
  k0 := (367082488558249/100000000000000000)
  k6 := (5783897341378863/500000000000000000)
  q := (83701851831366311773/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14012]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14012]

theorem width_14013 : mW 14013 = 325730875831750 := by
  have hu : mW 14013 ≤ 325730875831750 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14013 ≤ 325730875831749 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14013 : RowArithmetic 14013 (140425837438070952929/125000000000000000000000) (609172654498917318445801/1000000000000000000000000) (7297237865896371/1000000000000000000000000) where
  r0 := (602841743199/1000000000000000000)
  k0 := (734125682986167/200000000000000000)
  k6 := (2891845480784823/250000000000000000)
  q := (4185241928491111731/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14013]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14013]

theorem width_14014 : mW 14014 = 325812240262315 := by
  have hu : mW 14014 ≤ 325812240262315 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14014 ≤ 325812240262314 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14014 : RowArithmetic 14014 (1123375359004278446281/1000000000000000000000000) (19036290744136900767557/31250000000000000000000) (729588203027497/100000000000000000000000) where
  r0 := (602777218689/1000000000000000000)
  k0 := (734086393763/200000000000000)
  k6 := (1156696920770171/100000000000000000)
  q := (20926956300427446537/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14014]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14014]

theorem width_14015 : mW 14015 = 325893619209023 := by
  have hu : mW 14015 ≤ 325893619209023 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14015 ≤ 325893619209022 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14015 : RowArithmetic 14015 (112334402599524728759/100000000000000000000000) (19035936085731808194087/31250000000000000000000) (455907909171487/62500000000000000000000) where
  r0 := (602712705689/1000000000000000000)
  k0 := (367023554722979/100000000000000000)
  k6 := (115665565364371/10000000000000000)
  q := (83710811727040372787/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14015]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14015]

theorem width_14016 : mW 14016 = 325975012673426 := by
  have hu : mW 14016 ≤ 325975012673426 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14016 ≤ 325975012673425 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14016 : RowArithmetic 14016 (1123312700475131386593/1000000000000000000000000) (609138607291660147900427/1000000000000000000000000) (3646585707592751/500000000000000000000000) where
  r0 := (120529640839/200000000000000000)
  k0 := (917509787541741/250000000000000000)
  k6 := (11566143909337583/1000000000000000000)
  q := (83713798145825398931/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14016]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14016]

theorem width_14017 : mW 14017 = 326056420657080 := by
  have hu : mW 14017 ≤ 326056420657080 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14017 ≤ 326056420657079 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14017 : RowArithmetic 14017 (1123281382441586593807/1000000000000000000000000) (152281815364184874195063/250000000000000000000000) (3645908317741363/500000000000000000000000) where
  r0 := (301291857103/500000000000000000)
  k0 := (733968555525483/200000000000000000)
  k6 := (11565731326395281/1000000000000000000)
  q := (41858392229038133471/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14017]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14017]

theorem width_14018 : mW 14018 = 326137843161538 := by
  have hu : mW 14018 ≤ 326137843161538 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14018 ≤ 326137843161537 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14018 : RowArithmetic 14018 (449300028756908577/400000000000000000000) (152278979309571964375229/250000000000000000000000) (1458092441503641/200000000000000000000000) where
  r0 := (602519235717/1000000000000000000)
  k0 := (1834823214799927/500000000000000000)
  k6 := (11565318787602319/1000000000000000000)
  q := (167439541327608754293/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14018]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14018]

theorem width_14019 : mW 14019 = 326219280188354 := by
  have hu : mW 14019 ≤ 326219280188354 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14019 ≤ 326219280188353 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14019 : RowArithmetic 14019 (28080469220621120537/25000000000000000000000) (609104574635937363696517/1000000000000000000000000) (7289108131174709/1000000000000000000000000) where
  r0 := (602454768727/1000000000000000000)
  k0 := (229340631630323/62500000000000000)
  k6 := (462596251718033/40000000000000000)
  q := (83722756763021127839/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14019]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14019]

theorem width_14020 : mW 14020 = 326300731739081 := by
  have hu : mW 14020 ≤ 326300731739081 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14020 ≤ 326300731739080 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14020 : RowArithmetic 14020 (1123187473236967136889/1000000000000000000000000) (6090932336493201321531/10000000000000000000000) (291510176253403/40000000000000000000000) where
  r0 := (37649394577/62500000000000000)
  k0 := (458656725884389/125000000000000000)
  k6 := (5782246921216463/500000000000000000)
  q := (83725742755737915281/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14020]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14020]

theorem width_14021 : mW 14021 = 326382197815275 := by
  have hu : mW 14021 ≤ 326382197815275 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14021 ≤ 326382197815274 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14021 : RowArithmetic 14021 (1123156185126297989337/1000000000000000000000000) (60908189427806848225811/100000000000000000000000) (7286401032882127/1000000000000000000000000) where
  r0 := (60232586923/100000000000000000)
  k0 := (1834528766283763/500000000000000000)
  k6 := (11564081436040753/1000000000000000000)
  q := (41864364320983066851/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14021]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14021]

theorem width_14022 : mW 14022 = 326463678418489 := by
  have hu : mW 14022 ≤ 326463678418489 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14022 ≤ 326463678418488 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14022 : RowArithmetic 14022 (22462498089809993147/20000000000000000000000) (30453527826090743504079/50000000000000000000000) (18212620026747/2500000000000000000000) where
  r0 := (602261436717/1000000000000000000)
  k0 := (45860766031927/12500000000000000)
  k6 := (11563669073766439/1000000000000000000)
  q := (837317144217171753/5000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14022]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14022]

theorem width_14023 : mW 14023 = 326545173550277 := by
  have hu : mW 14023 ≤ 326545173550277 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14023 ≤ 326545173550276 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14023 : RowArithmetic 14023 (140386703915904346753/125000000000000000000000) (38066201273761983472563/62500000000000000000000) (7283695339668059/1000000000000000000000000) where
  r0 := (602197015691/1000000000000000000)
  k0 := (3668665057032851/1000000000000000000)
  k6 := (11563256755602119/1000000000000000000)
  q := (83734700095002430241/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14023]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14023]

theorem width_14024 : mW 14024 = 326626683212193 := by
  have hu : mW 14024 ≤ 326626683212193 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14024 ≤ 326626683212192 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14024 : RowArithmetic 14024 (1123062365634166907319/1000000000000000000000000) (15226197146320795851729/25000000000000000000000) (1820585754918229/250000000000000000000000) where
  r0 := (150533151537/250000000000000000)
  k0 := (1834234427997673/500000000000000000)
  k6 := (11562844481539929/1000000000000000000)
  q := (41868842830916643331/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14024]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14024]

theorem width_14025 : mW 14025 = 326708207405792 := by
  have hu : mW 14025 ≤ 326708207405792 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14025 ≤ 326708207405791 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14025 : RowArithmetic 14025 (1123031107408959980247/1000000000000000000000000) (121807310587873567456203/200000000000000000000000) (7280991050596411/1000000000000000000000000) where
  r0 := (602068208087/1000000000000000000)
  k0 := (3668272679442527/1000000000000000000)
  k6 := (1445304031446501/125000000000000000)
  q := (167481342244442261337/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14025]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14025]

theorem width_14026 : mW 14026 = 326789746132629 := by
  have hu : mW 14026 ≤ 326789746132629 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14026 ≤ 326789746132628 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14026 : RowArithmetic 14026 (1122999856649278850679/1000000000000000000000000) (304512610819716320002839/500000000000000000000000) (7279639432321631/1000000000000000000000000) where
  r0 := (9406309711/15625000000000000)
  k0 := (733615305473227/200000000000000000)
  k6 := (2312404013138099/200000000000000000)
  q := (83743656476177346337/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14026]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14026]

theorem width_14027 : mW 14027 = 326871299394256 := by
  have hu : mW 14027 ≤ 326871299394256 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14027 ≤ 326871299394255 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14027 : RowArithmetic 14027 (1122968613352791047407/1000000000000000000000000) (15225347298816481473913/25000000000000000000000) (363914408236589/50000000000000000000000) where
  r0 := (150484861599/250000000000000000)
  k0 := (1833940199880479/500000000000000000)
  k6 := (5780803961943767/500000000000000000)
  q := (167493283447426631431/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14027]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14027]

theorem width_14028 : mW 14028 = 326952867192230 := by
  have hu : mW 14028 ≤ 326952867192230 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14028 ≤ 326952867192229 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14028 : RowArithmetic 14028 (1122937377517162137199/1000000000000000000000000) (152250640969670192866869/250000000000000000000000) (3638468623854999/500000000000000000000000) where
  r0 := (601875082761/1000000000000000000)
  k0 := (3667684296624827/1000000000000000000)
  k6 := (11561195826155269/1000000000000000000)
  q := (41874813432420209411/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14028]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14028]

theorem width_14029 : mW 14029 = 327034449528104 := by
  have hu : mW 14029 ≤ 327034449528104 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14029 ≤ 327034449528103 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14029 : RowArithmetic 14029 (1122906149140060935621/1000000000000000000000000) (608991237417130381052491/1000000000000000000000000) (1455117336227913/200000000000000000000000) where
  r0 := (120362146119/200000000000000000)
  k0 := (91687205448737/25000000000000000)
  k6 := (11560783772485847/1000000000000000000)
  q := (167505223799140067297/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14029]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14029]

theorem width_14030 : mW 14030 = 327116046403433 := by
  have hu : mW 14030 ≤ 327116046403433 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14030 ≤ 327116046403432 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14030 : RowArithmetic 14030 (561437464109578016499/500000000000000000000000) (608979912567641402394809/1000000000000000000000000) (7274236464903763/1000000000000000000000000) where
  r0 := (75218298737/125000000000000000)
  k0 := (1833646081866373/500000000000000000)
  k6 := (2312074352574283/200000000000000000)
  q := (83755596827913536157/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14030]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14030]

theorem width_14031 : mW 14031 = 327197657819771 := by
  have hu : mW 14031 ≤ 327197657819771 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14031 ≤ 327197657819770 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14031 : RowArithmetic 14031 (1122843714752117529991/1000000000000000000000000) (608968589329847372017973/1000000000000000000000000) (1454577319777189/200000000000000000000000) where
  r0 := (30084103033/50000000000000000)
  k0 := (3667096133966357/1000000000000000000)
  k6 := (11559959797304123/1000000000000000000)
  q := (167517163299764600569/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14031]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14031]

theorem width_14032 : mW 14032 = 327279283778674 := by
  have hu : mW 14032 ≤ 327279283778674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14032 ≤ 327279283778673 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14032 : RowArithmetic 14032 (280703127184153825743/250000000000000000000000) (121791453540676349683887/200000000000000000000000) (7271537082969471/1000000000000000000000000) where
  r0 := (300808871443/500000000000000000)
  k0 := (3666900128651189/1000000000000000000)
  k6 := (92476383006209/8000000000000000)
  q := (167523132730975395881/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14032]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14032]

theorem width_14033 : mW 14033 = 327360924281696 := by
  have hu : mW 14033 ≤ 327360924281696 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14033 ≤ 327360924281695 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14033 : RowArithmetic 14033 (1122781310170321315577/1000000000000000000000000) (121789189537575651874571/200000000000000000000000) (727018791703779/100000000000000000000000) where
  r0 := (601553436569/1000000000000000000)
  k0 := (1833352073887961/500000000000000000)
  k6 := (462365439931183/40000000000000000)
  q := (167529101949482198017/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14033]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14033]

theorem width_14034 : mW 14034 = 327442579330391 := by
  have hu : mW 14034 ≤ 327442579330391 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14034 ≤ 327442579330390 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14034 : RowArithmetic 14034 (1122750119050908461483/1000000000000000000000000) (608934629282970657854393/1000000000000000000000000) (7268839100974403/1000000000000000000000000) where
  r0 := (150372285427/250000000000000000)
  k0 := (366650819134143/100000000000000000)
  k6 := (11558724164806627/1000000000000000000)
  q := (83767535477653871347/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14034]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14034]

theorem width_14035 : mW 14035 = 327524248926315 := by
  have hu : mW 14035 ≤ 327524248926315 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14035 ≤ 327524248926314 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14035 : RowArithmetic 14035 (1122718935376049410083/1000000000000000000000000) (60892331248829287601399/100000000000000000000000) (7267490634662813/1000000000000000000000000) where
  r0 := (6014248583/10000000000000000)
  k0 := (1833156129671243/500000000000000000)
  k6 := (5779156187674721/500000000000000000)
  q := (83770519874237380789/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14035]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14035]

theorem width_14036 : mW 14036 = 327605933071022 := by
  have hu : mW 14036 ≤ 327605933071022 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14036 ≤ 327605933071021 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14036 : RowArithmetic 14036 (1122687759143418915147/1000000000000000000000000) (76113999662934865369149/125000000000000000000000) (908267814748327/125000000000000000000000) where
  r0 := (30068029317/50000000000000000)
  k0 := (3666116351767767/1000000000000000000)
  k6 := (11557900629900177/1000000000000000000)
  q := (33509401665801196457/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14036]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14036]

theorem width_14037 : mW 14037 = 327687631766068 := by
  have hu : mW 14037 ≤ 327687631766068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14037 ≤ 327687631766067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14037 : RowArithmetic 14037 (561328295175345753077/500000000000000000000000) (608900683728162938094633/1000000000000000000000000) (3632397375414707/500000000000000000000000) where
  r0 := (150324081457/250000000000000000)
  k0 := (366592046862119/100000000000000000)
  k6 := (11557488928450997/1000000000000000000)
  q := (83776488348462064193/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14037]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14037]

theorem width_14038 : mW 14038 = 327769345013007 := by
  have hu : mW 14038 ≤ 327769345013007 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14038 ≤ 327769345013006 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14038 : RowArithmetic 14038 (280656357248885948761/250000000000000000000000) (304444685880989560060829/500000000000000000000000) (72634473330749/10000000000000000000000) where
  r0 := (601232076759/1000000000000000000)
  k0 := (3665724609891427/1000000000000000000)
  k6 := (722317329437129/62500000000000000)
  q := (83779472426125959701/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14038]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14038]

theorem width_14039 : mW 14039 = 327851072813394 := by
  have hu : mW 14039 ≤ 327851072813394 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14039 ≤ 327851072813393 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14039 : RowArithmetic 14039 (1122594275075652745437/1000000000000000000000000) (304439030702280950632817/500000000000000000000000) (1452420052921359/200000000000000000000000) where
  r0 := (601167839131/1000000000000000000)
  k0 := (733105755115259/200000000000000000)
  k6 := (2311333131504309/200000000000000000)
  q := (167564912795012070809/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14039]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14039]

theorem width_14040 : mW 14040 = 327932815168785 := by
  have hu : mW 14040 ≤ 327932815168785 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14040 ≤ 327932815168784 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14040 : RowArithmetic 14040 (561281564294347836673/500000000000000000000000) (12177335053110913305267/20000000000000000000000) (1815188386327211/250000000000000000000000) where
  r0 := (300551806471/500000000000000000)
  k0 := (366533296567361/100000000000000000)
  k6 := (11556254088025607/1000000000000000000)
  q := (167570880525227294039/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14040]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14040]

theorem width_14041 : mW 14041 = 328014572080735 := by
  have hu : mW 14041 ≤ 328014572080735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14041 ≤ 328014572080734 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14041 : RowArithmetic 14041 (1122531989532351398879/1000000000000000000000000) (121771089102913015282231/200000000000000000000000) (1451881435012973/200000000000000000000000) where
  r0 := (150259849547/250000000000000000)
  k0 := (3665137180175089/1000000000000000000)
  k6 := (11555842562498421/1000000000000000000)
  q := (167576848042920296479/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14041]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14041]

theorem width_14042 : mW 14042 = 328096343550798 := by
  have hu : mW 14042 ≤ 328096343550798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14042 ≤ 328096343550797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14042 : RowArithmetic 14042 (1122500857904300244569/1000000000000000000000000) (608844139981254773006087/1000000000000000000000000) (907257644219843/125000000000000000000000) where
  r0 := (300487597433/500000000000000000)
  k0 := (732988283815099/200000000000000000)
  k6 := (11555431080932157/1000000000000000000)
  q := (167582815348113781473/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14042]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14042]

theorem width_14043 : mW 14043 = 328178129580531 := by
  have hu : mW 14043 ≤ 328178129580531 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14043 ≤ 328178129580530 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14043 : RowArithmetic 14043 (280617433425555433409/250000000000000000000000) (121766567211049920829493/200000000000000000000000) (453544717579647/62500000000000000000000) where
  r0 := (600911002973/1000000000000000000)
  k0 := (366474568236959/100000000000000000)
  k6 := (1155501964331899/100000000000000000)
  q := (167588782440830448323/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14043]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14043]

theorem width_14044 : mW 14044 = 328259930171488 := by
  have hu : mW 14044 ≤ 328259930171488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14044 ≤ 328259930171487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14044 : RowArithmetic 14044 (140304827115474755219/125000000000000000000000) (608821533736184521522259/1000000000000000000000000) (906921269686959/125000000000000000000000) where
  r0 := (150211705627/250000000000000000)
  k0 := (1832274985029117/500000000000000000)
  k6 := (1444326031206387/125000000000000000)
  q := (16759474932109299229/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14044]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14044]

theorem width_14045 : mW 14045 = 328341745325225 := by
  have hu : mW 14045 ≤ 328341745325225 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14045 ≤ 328341745325224 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14045 : RowArithmetic 14045 (224481501513342224059/200000000000000000000000) (608810233023694500056021/1000000000000000000000000) (7254025182306693/1000000000000000000000000) where
  r0 := (300391326733/500000000000000000)
  k0 := (3664354282130087/1000000000000000000)
  k6 := (2888549224980163/250000000000000000)
  q := (41900178997231026149/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14045]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14045]

theorem width_14046 : mW 14046 = 328423575043297 := by
  have hu : mW 14046 ≤ 328423575043297 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14046 ≤ 328423575043296 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14046 : RowArithmetic 14046 (1122376405628644421149/1000000000000000000000000) (304399466958707368931517/500000000000000000000000) (3626340277795737/500000000000000000000000) where
  r0 := (120143699169/200000000000000000)
  k0 := (916039654645739/250000000000000000)
  k6 := (11553785594119837/1000000000000000000)
  q := (20950835305543309053/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14046]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14046]

theorem width_14047 : mW 14047 = 328505419327260 := by
  have hu : mW 14047 ≤ 328505419327260 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14047 ≤ 328505419327259 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14047 : RowArithmetic 14047 (28058632777682043673/25000000000000000000000) (121757527283396097920981/200000000000000000000000) (7251336277234099/1000000000000000000000000) where
  r0 := (600654349643/1000000000000000000)
  k0 := (3663962979414647/1000000000000000000)
  k6 := (5776687166120417/500000000000000000)
  q := (167612648687382778917/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14047]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14047]

theorem width_14048 : mW 14048 = 328587278178669 := by
  have hu : mW 14048 ≤ 328587278178669 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14048 ≤ 328587278178668 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14048 : RowArithmetic 14048 (280578556000077099823/250000000000000000000000) (152194085130506790472593/250000000000000000000000) (7249992347118723/1000000000000000000000000) where
  r0 := (75073776857/125000000000000000)
  k0 := (114492730144277/31250000000000000)
  k6 := (462118524571033/40000000000000000)
  q := (167618614718055703183/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14048]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14048]

theorem width_14049 : mW 14049 = 328669151599080 := by
  have hu : mW 14049 ≤ 328669151599080 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14049 ≤ 328669151599079 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14049 : RowArithmetic 14049 (1122283144305410030187/1000000000000000000000000) (608765046232190188951403/1000000000000000000000000) (7248648765129529/1000000000000000000000000) where
  r0 := (600526091481/1000000000000000000)
  k0 := (1831785887092181/500000000000000000)
  k6 := (11552551940216997/1000000000000000000)
  q := (167624580536387920293/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14049]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14049]

theorem width_14050 : mW 14050 = 328751039590049 := by
  have hu : mW 14050 ≤ 328751039590049 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14050 ≤ 328751039590048 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14050 : RowArithmetic 14050 (140281509002534151979/125000000000000000000000) (152188438386776314255351/250000000000000000000000) (1449461106230149/200000000000000000000000) where
  r0 := (150115494879/250000000000000000)
  k0 := (3663376208114941/1000000000000000000)
  k6 := (1444017601257067/125000000000000000)
  q := (33526109228480420257/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14050]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14050]

theorem width_14051 : mW 14051 = 328832942153131 := by
  have hu : mW 14051 ≤ 328832942153131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14051 ≤ 328832942153130 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14051 : RowArithmetic 14051 (561110503571293014693/500000000000000000000000) (608742462466408024748487/1000000000000000000000000) (452872665316667/62500000000000000000000) where
  r0 := (300198939479/500000000000000000)
  k0 := (457897583300419/125000000000000000)
  k6 := (1443966215473329/125000000000000000)
  q := (167636511536120913161/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14051]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14051]

theorem width_14052 : mW 14052 = 328914859289883 := by
  have hu : mW 14052 ≤ 328914859289883 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14052 ≤ 328914859289882 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14052 : RowArithmetic 14052 (1122189949670036320661/1000000000000000000000000) (12174623459794687283723/20000000000000000000000) (7244620106761613/1000000000000000000000000) where
  r0 := (600333789803/1000000000000000000)
  k0 := (915746287260323/250000000000000000)
  k6 := (462052747255979/40000000000000000)
  q := (16764247671756701889/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14052]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14052]

theorem width_14053 : mW 14053 = 328996791001859 := by
  have hu : mW 14053 ≤ 328996791001859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14053 ≤ 328996791001858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14053 : RowArithmetic 14053 (561079449800157290599/500000000000000000000000) (304359942558360106678989/500000000000000000000000) (1810819479029997/250000000000000000000000) where
  r0 := (12005394241/20000000000000000)
  k0 := (3662789656029609/1000000000000000000)
  k6 := (11550907682887261/1000000000000000000)
  q := (167648441686763077411/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14053]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14053]

theorem width_14054 : mW 14054 = 329078737290616 := by
  have hu : mW 14054 ≤ 329078737290616 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14054 ≤ 329078737290615 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14054 : RowArithmetic 14054 (14026598211638881323/12500000000000000000000) (608708598847001628719503/1000000000000000000000000) (1448387214605239/200000000000000000000000) where
  r0 := (120041129139/200000000000000000)
  k0 := (3662594187359999/1000000000000000000)
  k6 := (5775248364121091/500000000000000000)
  q := (16765440644373174363/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14054]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14054]

theorem width_14055 : mW 14055 = 329160698157709 := by
  have hu : mW 14055 ≤ 329160698157709 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14055 ≤ 329160698157708 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14055 : RowArithmetic 14055 (1122096821660115856623/1000000000000000000000000) (608697314180214797643997/1000000000000000000000000) (7240594577364729/1000000000000000000000000) where
  r0 := (37508849421/62500000000000000)
  k0 := (3662398743030257/1000000000000000000)
  k6 := (11550085817456437/1000000000000000000)
  q := (6706414839539826737/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14055]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14055]

theorem width_14056 : mW 14056 = 329242673604696 := by
  have hu : mW 14056 ≤ 329242673604696 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14056 ≤ 329242673604695 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14056 : RowArithmetic 14056 (1122065793785021600311/1000000000000000000000000) (152171507778999000170379/250000000000000000000000) (3619626714510031/500000000000000000000000) where
  r0 := (600077547169/1000000000000000000)
  k0 := (457775415379009/125000000000000000)
  k6 := (461986998020889/40000000000000000)
  q := (41916583830269374661/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14056]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14056]

theorem width_14057 : mW 14057 = 329324663633131 := by
  have hu : mW 14057 ≤ 329324663633131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14057 ≤ 329324663633130 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14057 : RowArithmetic 14057 (1122034773303521913277/1000000000000000000000000) (30433737482699081022487/50000000000000000000000) (3618956313938403/500000000000000000000000) where
  r0 := (37500844687/62500000000000000)
  k0 := (3662007927363239/1000000000000000000)
  k6 := (5774632063715873/500000000000000000)
  q := (83836149720749938553/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14057]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14057]

theorem width_14058 : mW 14058 = 329406668244571 := by
  have hu : mW 14058 ≤ 329406668244571 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14058 ≤ 329406668244570 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14058 : RowArithmetic 14058 (140250470026663772019/125000000000000000000000) (608663469793808186461501/1000000000000000000000000) (3618286086909777/500000000000000000000000) where
  r0 := (299974747101/500000000000000000)
  k0 := (732362511203699/200000000000000000)
  k6 := (2887213337044301/250000000000000000)
  q := (83839131674892721303/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14058]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14058]

theorem width_14059 : mW 14059 = 329488687440572 := by
  have hu : mW 14059 ≤ 329488687440572 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14059 ≤ 329488687440571 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14059 : RowArithmetic 14059 (224394550902416252349/200000000000000000000000) (152163047883778087454119/250000000000000000000000) (904404008341621/125000000000000000000000) where
  r0 := (149971371199/250000000000000000)
  k0 := (3661617208992579/1000000000000000000)
  k6 := (11548442612750803/1000000000000000000)
  q := (167684227045956829911/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14059]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14059]

theorem width_14060 : mW 14060 = 329570721222690 := by
  have hu : mW 14060 ≤ 329570721222690 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14060 ≤ 329570721222689 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14060 : RowArithmetic 14060 (1121941756197530962413/1000000000000000000000000) (608640914877530830291757/1000000000000000000000000) (3616946153250879/500000000000000000000000) where
  r0 := (149955371693/250000000000000000)
  k0 := (3661421886283279/1000000000000000000)
  k6 := (46192127684579/4000000000000000)
  q := (41922547632509167441/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14060]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14060]

theorem width_14061 : mW 14061 = 329652769592481 := by
  have hu : mW 14061 ≤ 329652769592481 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14061 ≤ 329652769592480 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14061 : RowArithmetic 14061 (112191076526735598959/100000000000000000000000) (304314819910350241880289/500000000000000000000000) (1808138223252671/250000000000000000000000) where
  r0 := (4798060001/8000000000000000)
  k0 := (146449063515169/40000000000000000)
  k6 := (5773810636675627/500000000000000000)
  q := (83848076901023794441/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14061]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14061]

theorem width_14062 : mW 14062 = 329734832551503 := by
  have hu : mW 14062 ≤ 329734832551503 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14062 ≤ 329734832551502 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14062 : RowArithmetic 14062 (224375956343850566461/200000000000000000000000) (60861836636425828248029/100000000000000000000000) (1807803456536127/250000000000000000000000) where
  r0 := (119938704971/200000000000000000)
  k0 := (915257828446077/250000000000000000)
  k6 := (5773605334681263/500000000000000000)
  q := (167702116862012209963/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14062]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14062]

theorem width_14063 : mW 14063 = 329816910101311 := by
  have hu : mW 14063 ≤ 329816910101311 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14063 ≤ 329816910101310 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14063 : RowArithmetic 14063 (560924402775460305201/500000000000000000000000) (608607094507841288234151/1000000000000000000000000) (7229875105788107/1000000000000000000000000) where
  r0 := (599629560957/1000000000000000000)
  k0 := (3660836063987153/1000000000000000000)
  k6 := (5773400054585389/500000000000000000)
  q := (167708079709953151679/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14063]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14063]

theorem width_14064 : mW 14064 = 329899002243461 := by
  have hu : mW 14064 ≤ 329899002243461 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14064 ≤ 329899002243460 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14064 : RowArithmetic 14064 (224363567352011758081/200000000000000000000000) (304297912125543362705189/500000000000000000000000) (3614268365913191/500000000000000000000000) where
  r0 := (599565608429/1000000000000000000)
  k0 := (732128167697109/200000000000000000)
  k6 := (360824674774007/31250000000000000)
  q := (41928510586473257171/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14064]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14064]

theorem width_14065 : mW 14065 = 329981108979510 := by
  have hu : mW 14065 ≤ 329981108979510 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14065 ≤ 329981108979509 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14065 : RowArithmetic 14065 (1121786875344367186227/1000000000000000000000000) (304292277796815942957593/500000000000000000000000) (7227198704144263/1000000000000000000000000) where
  r0 := (149875416817/250000000000000000)
  k0 := (3660445637274211/1000000000000000000)
  k6 := (5772989560073541/500000000000000000)
  q := (41930001192463612903/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14065]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14065]

theorem width_14066 : mW 14066 = 330063230311015 := by
  have hu : mW 14066 ≤ 330063230311015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14066 ≤ 330063230311014 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14066 : RowArithmetic 14066 (224351184260309305887/200000000000000000000000) (608573288535114155720103/1000000000000000000000000) (289034440905069/40000000000000000000000) where
  r0 := (599437737471/1000000000000000000)
  k0 := (1830125230173939/500000000000000000)
  k6 := (1154556869129957/100000000000000000)
  q := (41931491745465006769/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14066]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14066]

theorem width_14067 : mW 14067 = 330145366239533 := by
  have hu : mW 14067 ≤ 330145366239533 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14067 ≤ 330145366239532 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14067 : RowArithmetic 14067 (44868998985171938751/40000000000000000000000) (608562023075171098030721/1000000000000000000000000) (7224523687158793/1000000000000000000000000) where
  r0 := (149843454759/250000000000000000)
  k0 := (146402212308173/40000000000000000)
  k6 := (11545158306217907/1000000000000000000)
  q := (20966491122741544709/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14067]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14067]

theorem width_14068 : mW 14068 = 330227516766619 := by
  have hu : mW 14068 ≤ 330227516766619 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14068 ≤ 330227516766618 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14068 : RowArithmetic 14068 (8973552282602613663/8000000000000000000000) (304275379606720176887093/500000000000000000000000) (3611593348812791/500000000000000000000000) where
  r0 := (14982747799/25000000000000000)
  k0 := (3659860179338277/1000000000000000000)
  k6 := (5772373982447159/500000000000000000)
  q := (83868945385047020991/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14068]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14068]

theorem width_14069 : mW 14069 = 330309681893831 := by
  have hu : mW 14069 ≤ 330309681893831 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14069 ≤ 330309681893830 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14069 : RowArithmetic 14069 (280415775846833539541/250000000000000000000000) (304269748474779834870807/500000000000000000000000) (722185005391219/100000000000000000000000) where
  r0 := (599246016239/1000000000000000000)
  k0 := (1829832537620701/500000000000000000)
  k6 := (180380276051891/15625000000000000)
  q := (167743852346367674567/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14069]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14069]

theorem width_14070 : mW 14070 = 330391861622725 := by
  have hu : mW 14070 ≤ 330391861622725 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14070 ≤ 330391861622724 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14070 : RowArithmetic 14070 (280408044703256446251/250000000000000000000000) (152132059070791733648317/250000000000000000000000) (3610256877951903/500000000000000000000000) where
  r0 := (18724441621/31250000000000000)
  k0 := (3573701167397/976562500000000)
  k6 := (5771963706745127/500000000000000000)
  q := (167749813710775845977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14070]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14070]

theorem width_14071 : mW 14071 = 330474055954859 := by
  have hu : mW 14071 ≤ 330474055954859 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14071 ≤ 330474055954858 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14071 : RowArithmetic 14071 (1121601261600106331353/1000000000000000000000000) (121703395442780020797729/200000000000000000000000) (7219177803485623/1000000000000000000000000) where
  r0 := (299559129427/500000000000000000)
  k0 := (3659274939846267/1000000000000000000)
  k6 := (5771758601697117/500000000000000000)
  q := (83877887431670571373/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14071]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14071]

theorem width_14072 : mW 14072 = 330556264891788 := by
  have hu : mW 14072 ≤ 330556264891788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14072 ≤ 330556264891787 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14072 : RowArithmetic 14072 (280392587936570790091/250000000000000000000000) (608505719741397276904973/1000000000000000000000000) (7217842196542949/1000000000000000000000000) where
  r0 := (2340056239/3906250000000000)
  k0 := (1829539954268723/500000000000000000)
  k6 := (2885776759256299/250000000000000000)
  q := (167761735804086147397/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14072]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14072]

theorem width_14073 : mW 14073 = 330638488435071 := by
  have hu : mW 14073 ≤ 330638488435071 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14073 ≤ 330638488435070 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14073 : RowArithmetic 14073 (1121539449249262276023/1000000000000000000000000) (608494463865296678735301/1000000000000000000000000) (144330138699221/20000000000000000000000) where
  r0 := (299495273429/500000000000000000)
  k0 := (1829442450739863/500000000000000000)
  k6 := (1154269691437537/100000000000000000)
  q := (4194192413325835961/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14073]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14073]

theorem width_14074 : mW 14074 = 330720726586264 := by
  have hu : mW 14074 ≤ 330720726586264 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14074 ≤ 330720726586263 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14074 : RowArithmetic 14074 (11215085541067523011/10000000000000000000000) (608483209585236612624989/1000000000000000000000000) (3607586009312653/500000000000000000000000) where
  r0 := (299463353937/500000000000000000)
  k0 := (914672479667719/250000000000000000)
  k6 := (11542286835436991/1000000000000000000)
  q := (83886828525102795187/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14074]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14074]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14000 then ⟨(280953702195227367387/250000000000000000000000), (304660180395427831229887/500000000000000000000000), (58519166581423/8000000000000000000000)⟩ else
  if n = 14001 then ⟨(561891685340282029781/500000000000000000000000), (121861797808459626203853/200000000000000000000000), (7313535399180661/1000000000000000000000000)⟩ else
  if n = 14002 then ⟨(561875970051014582951/500000000000000000000000), (609297618916112179350469/1000000000000000000000000), (228505479040747/31250000000000000000000)⟩ else
  if n = 14003 then ⟨(1123720517042948628367/1000000000000000000000000), (609286250411927995819799/1000000000000000000000000), (1827703903232397/250000000000000000000000)⟩ else
  if n = 14004 then ⟨(561844550750484200079/500000000000000000000000), (152318720882343989473923/250000000000000000000000), (7309456249939787/1000000000000000000000000)⟩ else
  if n = 14005 then ⟨(112365769347373420829/100000000000000000000000), (609263518268086507201429/1000000000000000000000000), (913512155027073/125000000000000000000000)⟩ else
  if n = 14006 then ⟨(140453286619861590423/125000000000000000000000), (304626077313845116967523/500000000000000000000000), (7306738583642109/1000000000000000000000000)⟩ else
  if n = 14007 then ⟨(561797449977046655109/500000000000000000000000), (60924079260781783232189/100000000000000000000000), (7305380280098607/1000000000000000000000000)⟩ else
  if n = 14008 then ⟨(224712702891396787907/200000000000000000000000), (609229432208100012178691/1000000000000000000000000), (1460804465893657/200000000000000000000000)⟩ else
  if n = 14009 then ⟨(1123532136465214691581/1000000000000000000000000), (152304518357041963409523/250000000000000000000000), (3651332365816721/500000000000000000000000)⟩ else
  if n = 14010 then ⟨(280875191494109001083/250000000000000000000000), (609206716267652277757869/1000000000000000000000000), (7301307486476407/1000000000000000000000000)⟩ else
  if n = 14011 then ⟨(561734701494150211177/500000000000000000000000), (609195360726184485517929/1000000000000000000000000), (7299950593879599/1000000000000000000000000)⟩ else
  if n = 14012 then ⟨(280859511874614920387/250000000000000000000000), (152296001700848917826437/250000000000000000000000), (3649297026862711/500000000000000000000000)⟩ else
  if n = 14013 then ⟨(140425837438070952929/125000000000000000000000), (609172654498917318445801/1000000000000000000000000), (7297237865896371/1000000000000000000000000)⟩ else
  if n = 14014 then ⟨(1123375359004278446281/1000000000000000000000000), (19036290744136900767557/31250000000000000000000), (729588203027497/100000000000000000000000)⟩ else
  if n = 14015 then ⟨(112334402599524728759/100000000000000000000000), (19035936085731808194087/31250000000000000000000), (455907909171487/62500000000000000000000)⟩ else
  if n = 14016 then ⟨(1123312700475131386593/1000000000000000000000000), (609138607291660147900427/1000000000000000000000000), (3646585707592751/500000000000000000000000)⟩ else
  if n = 14017 then ⟨(1123281382441586593807/1000000000000000000000000), (152281815364184874195063/250000000000000000000000), (3645908317741363/500000000000000000000000)⟩ else
  if n = 14018 then ⟨(449300028756908577/400000000000000000000), (152278979309571964375229/250000000000000000000000), (1458092441503641/200000000000000000000000)⟩ else
  if n = 14019 then ⟨(28080469220621120537/25000000000000000000000), (609104574635937363696517/1000000000000000000000000), (7289108131174709/1000000000000000000000000)⟩ else
  if n = 14020 then ⟨(1123187473236967136889/1000000000000000000000000), (6090932336493201321531/10000000000000000000000), (291510176253403/40000000000000000000000)⟩ else
  if n = 14021 then ⟨(1123156185126297989337/1000000000000000000000000), (60908189427806848225811/100000000000000000000000), (7286401032882127/1000000000000000000000000)⟩ else
  if n = 14022 then ⟨(22462498089809993147/20000000000000000000000), (30453527826090743504079/50000000000000000000000), (18212620026747/2500000000000000000000)⟩ else
  if n = 14023 then ⟨(140386703915904346753/125000000000000000000000), (38066201273761983472563/62500000000000000000000), (7283695339668059/1000000000000000000000000)⟩ else
  if n = 14024 then ⟨(1123062365634166907319/1000000000000000000000000), (15226197146320795851729/25000000000000000000000), (1820585754918229/250000000000000000000000)⟩ else
  if n = 14025 then ⟨(1123031107408959980247/1000000000000000000000000), (121807310587873567456203/200000000000000000000000), (7280991050596411/1000000000000000000000000)⟩ else
  if n = 14026 then ⟨(1122999856649278850679/1000000000000000000000000), (304512610819716320002839/500000000000000000000000), (7279639432321631/1000000000000000000000000)⟩ else
  if n = 14027 then ⟨(1122968613352791047407/1000000000000000000000000), (15225347298816481473913/25000000000000000000000), (363914408236589/50000000000000000000000)⟩ else
  if n = 14028 then ⟨(1122937377517162137199/1000000000000000000000000), (152250640969670192866869/250000000000000000000000), (3638468623854999/500000000000000000000000)⟩ else
  if n = 14029 then ⟨(1122906149140060935621/1000000000000000000000000), (608991237417130381052491/1000000000000000000000000), (1455117336227913/200000000000000000000000)⟩ else
  if n = 14030 then ⟨(561437464109578016499/500000000000000000000000), (608979912567641402394809/1000000000000000000000000), (7274236464903763/1000000000000000000000000)⟩ else
  if n = 14031 then ⟨(1122843714752117529991/1000000000000000000000000), (608968589329847372017973/1000000000000000000000000), (1454577319777189/200000000000000000000000)⟩ else
  if n = 14032 then ⟨(280703127184153825743/250000000000000000000000), (121791453540676349683887/200000000000000000000000), (7271537082969471/1000000000000000000000000)⟩ else
  if n = 14033 then ⟨(1122781310170321315577/1000000000000000000000000), (121789189537575651874571/200000000000000000000000), (727018791703779/100000000000000000000000)⟩ else
  if n = 14034 then ⟨(1122750119050908461483/1000000000000000000000000), (608934629282970657854393/1000000000000000000000000), (7268839100974403/1000000000000000000000000)⟩ else
  if n = 14035 then ⟨(1122718935376049410083/1000000000000000000000000), (60892331248829287601399/100000000000000000000000), (7267490634662813/1000000000000000000000000)⟩ else
  if n = 14036 then ⟨(1122687759143418915147/1000000000000000000000000), (76113999662934865369149/125000000000000000000000), (908267814748327/125000000000000000000000)⟩ else
  if n = 14037 then ⟨(561328295175345753077/500000000000000000000000), (608900683728162938094633/1000000000000000000000000), (3632397375414707/500000000000000000000000)⟩ else
  if n = 14038 then ⟨(280656357248885948761/250000000000000000000000), (304444685880989560060829/500000000000000000000000), (72634473330749/10000000000000000000000)⟩ else
  if n = 14039 then ⟨(1122594275075652745437/1000000000000000000000000), (304439030702280950632817/500000000000000000000000), (1452420052921359/200000000000000000000000)⟩ else
  if n = 14040 then ⟨(561281564294347836673/500000000000000000000000), (12177335053110913305267/20000000000000000000000), (1815188386327211/250000000000000000000000)⟩ else
  if n = 14041 then ⟨(1122531989532351398879/1000000000000000000000000), (121771089102913015282231/200000000000000000000000), (1451881435012973/200000000000000000000000)⟩ else
  if n = 14042 then ⟨(1122500857904300244569/1000000000000000000000000), (608844139981254773006087/1000000000000000000000000), (907257644219843/125000000000000000000000)⟩ else
  if n = 14043 then ⟨(280617433425555433409/250000000000000000000000), (121766567211049920829493/200000000000000000000000), (453544717579647/62500000000000000000000)⟩ else
  if n = 14044 then ⟨(140304827115474755219/125000000000000000000000), (608821533736184521522259/1000000000000000000000000), (906921269686959/125000000000000000000000)⟩ else
  if n = 14045 then ⟨(224481501513342224059/200000000000000000000000), (608810233023694500056021/1000000000000000000000000), (7254025182306693/1000000000000000000000000)⟩ else
  if n = 14046 then ⟨(1122376405628644421149/1000000000000000000000000), (304399466958707368931517/500000000000000000000000), (3626340277795737/500000000000000000000000)⟩ else
  if n = 14047 then ⟨(28058632777682043673/25000000000000000000000), (121757527283396097920981/200000000000000000000000), (7251336277234099/1000000000000000000000000)⟩ else
  if n = 14048 then ⟨(280578556000077099823/250000000000000000000000), (152194085130506790472593/250000000000000000000000), (7249992347118723/1000000000000000000000000)⟩ else
  if n = 14049 then ⟨(1122283144305410030187/1000000000000000000000000), (608765046232190188951403/1000000000000000000000000), (7248648765129529/1000000000000000000000000)⟩ else
  if n = 14050 then ⟨(140281509002534151979/125000000000000000000000), (152188438386776314255351/250000000000000000000000), (1449461106230149/200000000000000000000000)⟩ else
  if n = 14051 then ⟨(561110503571293014693/500000000000000000000000), (608742462466408024748487/1000000000000000000000000), (452872665316667/62500000000000000000000)⟩ else
  if n = 14052 then ⟨(1122189949670036320661/1000000000000000000000000), (12174623459794687283723/20000000000000000000000), (7244620106761613/1000000000000000000000000)⟩ else
  if n = 14053 then ⟨(561079449800157290599/500000000000000000000000), (304359942558360106678989/500000000000000000000000), (1810819479029997/250000000000000000000000)⟩ else
  if n = 14054 then ⟨(14026598211638881323/12500000000000000000000), (608708598847001628719503/1000000000000000000000000), (1448387214605239/200000000000000000000000)⟩ else
  if n = 14055 then ⟨(1122096821660115856623/1000000000000000000000000), (608697314180214797643997/1000000000000000000000000), (7240594577364729/1000000000000000000000000)⟩ else
  if n = 14056 then ⟨(1122065793785021600311/1000000000000000000000000), (152171507778999000170379/250000000000000000000000), (3619626714510031/500000000000000000000000)⟩ else
  if n = 14057 then ⟨(1122034773303521913277/1000000000000000000000000), (30433737482699081022487/50000000000000000000000), (3618956313938403/500000000000000000000000)⟩ else
  if n = 14058 then ⟨(140250470026663772019/125000000000000000000000), (608663469793808186461501/1000000000000000000000000), (3618286086909777/500000000000000000000000)⟩ else
  if n = 14059 then ⟨(224394550902416252349/200000000000000000000000), (152163047883778087454119/250000000000000000000000), (904404008341621/125000000000000000000000)⟩ else
  if n = 14060 then ⟨(1121941756197530962413/1000000000000000000000000), (608640914877530830291757/1000000000000000000000000), (3616946153250879/500000000000000000000000)⟩ else
  if n = 14061 then ⟨(112191076526735598959/100000000000000000000000), (304314819910350241880289/500000000000000000000000), (1808138223252671/250000000000000000000000)⟩ else
  if n = 14062 then ⟨(224375956343850566461/200000000000000000000000), (60861836636425828248029/100000000000000000000000), (1807803456536127/250000000000000000000000)⟩ else
  if n = 14063 then ⟨(560924402775460305201/500000000000000000000000), (608607094507841288234151/1000000000000000000000000), (7229875105788107/1000000000000000000000000)⟩ else
  if n = 14064 then ⟨(224363567352011758081/200000000000000000000000), (304297912125543362705189/500000000000000000000000), (3614268365913191/500000000000000000000000)⟩ else
  if n = 14065 then ⟨(1121786875344367186227/1000000000000000000000000), (304292277796815942957593/500000000000000000000000), (7227198704144263/1000000000000000000000000)⟩ else
  if n = 14066 then ⟨(224351184260309305887/200000000000000000000000), (608573288535114155720103/1000000000000000000000000), (289034440905069/40000000000000000000000)⟩ else
  if n = 14067 then ⟨(44868998985171938751/40000000000000000000000), (608562023075171098030721/1000000000000000000000000), (7224523687158793/1000000000000000000000000)⟩ else
  if n = 14068 then ⟨(8973552282602613663/8000000000000000000000), (304275379606720176887093/500000000000000000000000), (3611593348812791/500000000000000000000000)⟩ else
  if n = 14069 then ⟨(280415775846833539541/250000000000000000000000), (304269748474779834870807/500000000000000000000000), (722185005391219/100000000000000000000000)⟩ else
  if n = 14070 then ⟨(280408044703256446251/250000000000000000000000), (152132059070791733648317/250000000000000000000000), (3610256877951903/500000000000000000000000)⟩ else
  if n = 14071 then ⟨(1121601261600106331353/1000000000000000000000000), (121703395442780020797729/200000000000000000000000), (7219177803485623/1000000000000000000000000)⟩ else
  if n = 14072 then ⟨(280392587936570790091/250000000000000000000000), (608505719741397276904973/1000000000000000000000000), (7217842196542949/1000000000000000000000000)⟩ else
  if n = 14073 then ⟨(1121539449249262276023/1000000000000000000000000), (608494463865296678735301/1000000000000000000000000), (144330138699221/20000000000000000000000)⟩ else
  ⟨(11215085541067523011/10000000000000000000000), (608483209585236612624989/1000000000000000000000000), (3607586009312653/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14000 ≤ n) (hb : n ≤ 14074) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14000
  · exact row_14001
  · exact row_14002
  · exact row_14003
  · exact row_14004
  · exact row_14005
  · exact row_14006
  · exact row_14007
  · exact row_14008
  · exact row_14009
  · exact row_14010
  · exact row_14011
  · exact row_14012
  · exact row_14013
  · exact row_14014
  · exact row_14015
  · exact row_14016
  · exact row_14017
  · exact row_14018
  · exact row_14019
  · exact row_14020
  · exact row_14021
  · exact row_14022
  · exact row_14023
  · exact row_14024
  · exact row_14025
  · exact row_14026
  · exact row_14027
  · exact row_14028
  · exact row_14029
  · exact row_14030
  · exact row_14031
  · exact row_14032
  · exact row_14033
  · exact row_14034
  · exact row_14035
  · exact row_14036
  · exact row_14037
  · exact row_14038
  · exact row_14039
  · exact row_14040
  · exact row_14041
  · exact row_14042
  · exact row_14043
  · exact row_14044
  · exact row_14045
  · exact row_14046
  · exact row_14047
  · exact row_14048
  · exact row_14049
  · exact row_14050
  · exact row_14051
  · exact row_14052
  · exact row_14053
  · exact row_14054
  · exact row_14055
  · exact row_14056
  · exact row_14057
  · exact row_14058
  · exact row_14059
  · exact row_14060
  · exact row_14061
  · exact row_14062
  · exact row_14063
  · exact row_14064
  · exact row_14065
  · exact row_14066
  · exact row_14067
  · exact row_14068
  · exact row_14069
  · exact row_14070
  · exact row_14071
  · exact row_14072
  · exact row_14073
  · exact row_14074

end BstLean.Part271.R3.Rows14000
