import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14312–14386. -/
namespace BstLean.Part271.R3.Rows14312
open Real BstLean.Part130 BstLean.Part227

theorem width_14312 : mW 14312 = 350712420290333 := by
  have hu : mW 14312 ≤ 350712420290333 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14312 ≤ 350712420290332 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14312 : RowArithmetic 14312 (557179791686063933799/500000000000000000000000) (151462319028649760176587/250000000000000000000000) (6907026460924519/1000000000000000000000000) where
  r0 := (584049301221/1000000000000000000)
  k0 := (722592606723577/200000000000000000)
  k6 := (5722956918059913/500000000000000000)
  q := (169186287860452804487/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14312]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14312]

theorem width_14313 : mW 14313 = 350798194513585 := by
  have hu : mW 14313 ≤ 350798194513585 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14313 ≤ 350798194513584 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14313 : RowArithmetic 14313 (557165191101512465379/500000000000000000000000) (605838393168156569167891/1000000000000000000000000) (6905770874543687/1000000000000000000000000) where
  r0 := (291994047011/500000000000000000)
  k0 := (3612773713006629/1000000000000000000)
  k6 := (11445513985852071/1000000000000000000)
  q := (169192198401699361571/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14313]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14313]

theorem width_14314 : mW 14314 = 350883983720019 := by
  have hu : mW 14314 ≤ 350883983720019 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14314 ≤ 350883983720018 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14314 : RowArithmetic 14314 (111430118786297323993/100000000000000000000000) (121165502346820308850597/200000000000000000000000) (1726128901797179/250000000000000000000000) where
  r0 := (72990862189/125000000000000000)
  k0 := (903146103884679/250000000000000000)
  k6 := (5722557088743181/500000000000000000)
  q := (169198108736474947633/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14314]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14314]

theorem width_14315 : mW 14315 = 350969787911205 := by
  have hu : mW 14315 ≤ 350969787911205 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14315 ≤ 350969787911204 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14315 : RowArithmetic 14315 (1114272000349882348481/1000000000000000000000000) (605816631812098233326057/1000000000000000000000000) (138065213175111/20000000000000000000000) where
  r0 := (583865711689/1000000000000000000)
  k0 := (3612395141211597/1000000000000000000)
  k6 := (572235720550769/50000000000000000)
  q := (84602009432400599453/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14315]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14315]

theorem width_14316 : mW 14316 = 351055607088714 := by
  have hu : mW 14316 ≤ 351055607088714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14316 ≤ 351055607088713 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14316 : RowArithmetic 14316 (1114242819661662114313/1000000000000000000000000) (605805753401810791823103/1000000000000000000000000) (862750753642519/125000000000000000000000) where
  r0 := (583804536551/1000000000000000000)
  k0 := (3612205890022723/1000000000000000000)
  k6 := (11444314686431809/1000000000000000000)
  q := (84604964393349873923/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14316]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14316]

theorem width_14317 : mW 14317 = 351141441254116 := by
  have hu : mW 14317 ≤ 351141441254116 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14317 ≤ 351141441254115 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14317 : RowArithmetic 14317 (111421364579622372807/100000000000000000000000) (605794876502903706910607/1000000000000000000000000) (6900751718238549/1000000000000000000000000) where
  r0 := (9120990189/15625000000000000)
  k0 := (451502082746193/125000000000000000)
  k6 := (2288783000745667/200000000000000000)
  q := (16921583850219222313/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14317]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14317]

theorem width_14318 : mW 14318 = 351227290408982 := by
  have hu : mW 14318 ≤ 351227290408982 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14318 ≤ 351227290408981 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14318 : RowArithmetic 14318 (557092239375739342261/500000000000000000000000) (30289200055752068487303/50000000000000000000000) (6899497725946791/1000000000000000000000000) where
  r0 := (583682218319/1000000000000000000)
  k0 := (112869608032507/31250000000000000)
  k6 := (5721757681448823/500000000000000000)
  q := (84610874005650124829/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14318]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14318]

theorem width_14319 : mW 14319 = 351313154554881 := by
  have hu : mW 14319 ≤ 351313154554881 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14319 ≤ 351313154554880 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14319 : RowArithmetic 14319 (222831063705068064661/200000000000000000000000) (302886563618944203001143/500000000000000000000000) (6898244052161009/1000000000000000000000000) where
  r0 := (29181053761/50000000000000000)
  k0 := (282159240253/78125000000000)
  k6 := (11443115763932429/1000000000000000000)
  q := (169227657314045448557/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14319]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14319]

theorem width_14320 : mW 14320 = 351399033693386 := by
  have hu : mW 14320 ≤ 351399033693386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14320 ≤ 351399033693385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14320 : RowArithmetic 14320 (1114126165115720747449/1000000000000000000000000) (605762254871109417415983/1000000000000000000000000) (6896990696777299/1000000000000000000000000) where
  r0 := (116711988559/200000000000000000)
  k0 := (3611449116555327/1000000000000000000)
  k6 := (11442716206825377/1000000000000000000)
  q := (6769342656417977487/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14320]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14320]

theorem width_14321 : mW 14321 = 351484927826065 := by
  have hu : mW 14321 ≤ 351484927826065 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14321 ≤ 351484927826064 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14321 : RowArithmetic 14321 (1114097018520535443719/1000000000000000000000000) (151437846003592318205097/250000000000000000000000) (6895737659691897/1000000000000000000000000) where
  r0 := (583498821041/1000000000000000000)
  k0 := (902814995246339/250000000000000000)
  k6 := (5721158345784591/500000000000000000)
  q := (16923947530053382909/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14321]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14321]

theorem width_14322 : mW 14322 = 351570836954490 := by
  have hu : mW 14322 ≤ 351570836954490 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14322 ≤ 351570836954489 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14322 : RowArithmetic 14322 (1114067878737698662283/1000000000000000000000000) (121148102933466559334793/200000000000000000000000) (6894484940801001/1000000000000000000000000) where
  r0 := (145859427489/250000000000000000)
  k0 := (3611070868525929/1000000000000000000)
  k6 := (5720958609078269/500000000000000000)
  q := (21155672998040029263/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14322]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14322]

theorem width_14323 : mW 14323 = 351656761080232 := by
  have hu : mW 14323 ≤ 351656761080232 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14323 ≤ 351656761080231 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14323 : RowArithmetic 14323 (1114038745765125983153/1000000000000000000000000) (605729646829665001638767/1000000000000000000000000) (55145860320007/8000000000000000000000) where
  r0 := (291688304769/500000000000000000)
  k0 := (1805440889587243/500000000000000000)
  k6 := (11441517786580143/1000000000000000000)
  q := (677005169847321033/4000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14323]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14323]

theorem width_14324 : mW 14324 = 351742700204861 := by
  have hu : mW 14324 ≤ 351742700204861 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14324 ≤ 351742700204860 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14324 : RowArithmetic 14324 (44560384784029372589/40000000000000000000000) (605718780501030978941853/1000000000000000000000000) (3445990228593921/500000000000000000000000) where
  r0 := (72914439973/125000000000000000)
  k0 := (28885541703403/8000000000000000)
  k6 := (11441118396832693/1000000000000000000)
  q := (84628600366542751893/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14324]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14324]

theorem width_14325 : mW 14325 = 351828654329948 := by
  have hu : mW 14325 ≤ 351828654329948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14325 ≤ 351828654329947 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14325 : RowArithmetic 14325 (1113980500242440868093/1000000000000000000000000) (302853957840547937554069/500000000000000000000000) (6890728692258247/1000000000000000000000000) where
  r0 := (583254440691/1000000000000000000)
  k0 := (1805251834886469/500000000000000000)
  k6 := (11440719048906889/1000000000000000000)
  q := (169263108798107569203/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14325]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14325]

theorem width_14326 : mW 14326 = 351914623457064 := by
  have hu : mW 14326 ≤ 351914623457064 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14326 ≤ 351914623457063 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14326 : RowArithmetic 14326 (69621961730510229349/62500000000000000000000) (605697052369525012378471/1000000000000000000000000) (5382404097741/781250000000000000000) where
  r0 := (18224792883/31250000000000000)
  k0 := (1805157324855759/500000000000000000)
  k6 := (11440319742795433/1000000000000000000)
  q := (169269016656918049221/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14326]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14326]

theorem width_14327 : mW 14327 = 352000607587780 := by
  have hu : mW 14327 ≤ 352000607587780 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14327 ≤ 352000607587779 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14327 : RowArithmetic 14327 (1113922281935821560347/1000000000000000000000000) (302843095282991890921063/500000000000000000000000) (1722056528908743/250000000000000000000000) where
  r0 := (291566157239/500000000000000000)
  k0 := (3610125652741647/1000000000000000000)
  k6 := (11439920478491027/1000000000000000000)
  q := (169274924309538534793/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14327]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14327]

theorem width_14328 : mW 14328 = 352086606723667 := by
  have hu : mW 14328 ≤ 352086606723667 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14328 ≤ 352086606723666 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14328 : RowArithmetic 14328 (1113893182983334195941/1000000000000000000000000) (302837665135068840378281/500000000000000000000000) (1721743825933549/250000000000000000000000) where
  r0 := (72883908419/125000000000000000)
  k0 := (3609936678851473/1000000000000000000)
  k6 := (5719760627993189/500000000000000000)
  q := (169280831755990613103/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14328]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14328]

theorem width_14329 : mW 14329 = 352172620866296 := by
  have hu : mW 14329 ≤ 352172620866296 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14329 ≤ 352172620866295 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14329 : RowArithmetic 14329 (1113864090828622045927/1000000000000000000000000) (605664471481652294336621/1000000000000000000000000) (1721431202325667/250000000000000000000000) where
  r0 := (291505115439/500000000000000000)
  k0 := (3609747728044621/1000000000000000000)
  k6 := (714945129704637/62500000000000000)
  q := (16928673899629586757/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14329]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14329]

theorem width_14330 : mW 14330 = 352258650017237 := by
  have hu : mW 14330 ≤ 352258650017237 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14330 ≤ 352258650017236 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14330 : RowArithmetic 14330 (111383500546960690453/100000000000000000000000) (302826807100096659194229/500000000000000000000000) (1376894926447393/200000000000000000000000) where
  r0 := (145737301263/250000000000000000)
  k0 := (902389700078083/250000000000000000)
  k6 := (5719361468173589/500000000000000000)
  q := (33858529206095175569/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14330]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14330]

theorem width_14331 : mW 14331 = 352344694178063 := by
  have hu : mW 14331 ≤ 352344694178063 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14331 ≤ 352344694178062 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14331 : RowArithmetic 14331 (556902963452104922853/500000000000000000000000) (605642758425426554514821/1000000000000000000000000) (430201548277103/62500000000000000000000) where
  r0 := (582888189871/1000000000000000000)
  k0 := (1804684947824471/500000000000000000)
  k6 := (11438323839198047/1000000000000000000)
  q := (84649276429276109909/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14331]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14331]

theorem width_14332 : mW 14332 = 352430753350344 := by
  have hu : mW 14332 ≤ 352430753350344 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14332 ≤ 352430753350343 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14332 : RowArithmetic 14332 (111377685513035428983/100000000000000000000000) (605631904157017912962183/1000000000000000000000000) (3440987614894689/500000000000000000000000) where
  r0 := (291413592667/500000000000000000)
  k0 := (56393453344609/15625000000000000)
  k6 := (11437924783819511/1000000000000000000)
  q := (169304459480546465611/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14332]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14332]

theorem width_14333 : mW 14333 = 352516827535652 := by
  have hu : mW 14333 ≤ 352516827535652 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14333 ≤ 352516827535651 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14333 : RowArithmetic 14333 (111374779014596344789/100000000000000000000000) (37851315712164584540413/62500000000000000000000) (6880726004200821/1000000000000000000000000) where
  r0 := (145691547859/250000000000000000)
  k0 := (1804496077759287/500000000000000000)
  k6 := (11437525770204283/1000000000000000000)
  q := (84655182948240091793/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14333]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14333]

theorem width_14334 : mW 14334 = 352602916735557 := by
  have hu : mW 14334 ≤ 352602916735557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14334 ≤ 352602916735556 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14334 : RowArithmetic 14334 (69607420746810147759/62500000000000000000000) (302805100068969510366199/500000000000000000000000) (3439738547782361/500000000000000000000000) where
  r0 := (582705208177/1000000000000000000)
  k0 := (3608803320043357/1000000000000000000)
  k6 := (11437126798345081/1000000000000000000)
  q := (169316272106374938343/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14334]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14334]

theorem width_14335 : mW 14335 = 352689020951632 := by
  have hu : mW 14335 ≤ 352689020951632 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14335 ≤ 352689020951631 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14335 : RowArithmetic 14335 (111368968053727536343/100000000000000000000000) (605599350386601114291489/1000000000000000000000000) (1719557125944453/250000000000000000000000) where
  r0 := (582644235553/1000000000000000000)
  k0 := (3608614507620557/1000000000000000000)
  k6 := (11436727868234621/1000000000000000000)
  q := (169322178110252290719/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14335]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14335]

theorem width_14336 : mW 14336 = 352775140185447 := by
  have hu : mW 14336 ≤ 352775140185447 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14336 ≤ 352775140185446 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14336 : RowArithmetic 14336 (1113660635908829112873/1000000000000000000000000) (605588502140285936114527/1000000000000000000000000) (6876980228736919/1000000000000000000000000) where
  r0 := (582583273561/1000000000000000000)
  k0 := (1804212859122251/500000000000000000)
  k6 := (1429541122483203/125000000000000000)
  q := (169328083908133797793/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14336]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14336]

theorem width_14337 : mW 14337 = 352861274438574 := by
  have hu : mW 14337 ≤ 352861274438574 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14337 ≤ 352861274438573 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14337 : RowArithmetic 14337 (278407899515387517557/250000000000000000000000) (605577655398659896287483/1000000000000000000000000) (3437866135169439/500000000000000000000000) where
  r0 := (582522322199/1000000000000000000)
  k0 := (3608236951912617/1000000000000000000)
  k6 := (1143593013323081/100000000000000000)
  q := (169333989500041012883/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14337]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14337]

theorem width_14338 : mW 14338 = 352947423712585 := by
  have hu : mW 14338 ≤ 352947423712585 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14338 ≤ 352947423712584 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14338 : RowArithmetic 14338 (1113602566993365504383/1000000000000000000000000) (75695851270173690149059/125000000000000000000000) (1718621157120141/250000000000000000000000) where
  r0 := (116492276293/200000000000000000)
  k0 := (3608048208622323/1000000000000000000)
  k6 := (5717765664161451/500000000000000000)
  q := (3386797897719909711/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14338]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14338]

theorem width_14339 : mW 14339 = 353033588009051 := by
  have hu : mW 14339 ≤ 353033588009051 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14339 ≤ 353033588009050 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14339 : RowArithmetic 14339 (556786771351102002081/500000000000000000000000) (302777983214070672554037/500000000000000000000000) (3436618651529457/500000000000000000000000) where
  r0 := (145600112839/250000000000000000)
  k0 := (450982436045993/125000000000000000)
  k6 := (91481060521077/8000000000000000)
  q := (84672900033009380799/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14339]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14339]

theorem width_14340 : mW 14340 = 353119767329544 := by
  have hu : mW 14340 ≤ 353119767329544 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14340 ≤ 353119767329543 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14340 : RowArithmetic 14340 (1113544525185994458871/1000000000000000000000000) (605545124198582197686841/1000000000000000000000000) (858998786746361/125000000000000000000000) where
  r0 := (145584882967/250000000000000000)
  k0 := (721534158228141/200000000000000000)
  k6 := (11434733843658707/1000000000000000000)
  q := (84675852520066191537/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14340]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14340]

theorem width_14341 : mW 14341 = 353205961675635 := by
  have hu : mW 14341 ≤ 353205961675635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14341 ≤ 353205961675634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14341 : RowArithmetic 14341 (1113515514442667076519/1000000000000000000000000) (302767141736189407190913/500000000000000000000000) (1374148720222701/200000000000000000000000) where
  r0 := (582278623001/1000000000000000000)
  k0 := (180374105847211/50000000000000000)
  k6 := (5717167581943937/500000000000000000)
  q := (42339402452089472067/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14341]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14341]

theorem width_14342 : mW 14342 = 353292171048897 := by
  have hu : mW 14342 ≤ 353292171048897 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14342 ≤ 353292171048896 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14342 : RowArithmetic 14342 (1113486510470151856597/1000000000000000000000000) (605523444249198110558683/1000000000000000000000000) (429343576523987/62500000000000000000000) where
  r0 := (2328870899/4000000000000000)
  k0 := (3607293465766613/1000000000000000000)
  k6 := (5716968262907429/500000000000000000)
  q := (84681757185358405859/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14342]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14342]

theorem width_14343 : mW 14343 = 353378395450901 := by
  have hu : mW 14343 ≤ 353378395450901 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14343 ≤ 353378395450900 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14343 : RowArithmetic 14343 (222691502653276125057/200000000000000000000000) (37844537908044196598639/62500000000000000000000) (6868251163678851/1000000000000000000000000) where
  r0 := (291078418557/500000000000000000)
  k0 := (3607104837608397/1000000000000000000)
  k6 := (1143353792943239/100000000000000000)
  q := (84684709363615342103/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14343]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14343]

theorem width_14344 : mW 14344 = 353464634883219 := by
  have hu : mW 14344 ≤ 353464634883219 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14344 ≤ 353464634883218 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14344 : RowArithmetic 14344 (69589282676830344277/62500000000000000000000) (302750885155286494348459/500000000000000000000000) (6867005418895811/1000000000000000000000000) where
  r0 := (58209596009/100000000000000000)
  k0 := (360691623246389/100000000000000000)
  k6 := (11433139374733203/1000000000000000000)
  q := (84687661438960516381/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14344]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14344]

theorem width_14345 : mW 14345 = 353550889347422 := by
  have hu : mW 14345 ≤ 353550889347422 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14345 ≤ 353550889347421 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14345 : RowArithmetic 14345 (556699769578399974067/500000000000000000000000) (605490935594462892793463/1000000000000000000000000) (6865759989931861/1000000000000000000000000) where
  r0 := (23281403747/40000000000000000)
  k0 := (1803363825163703/500000000000000000)
  k6 := (5716370430855017/500000000000000000)
  q := (84690613411404690333/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14345]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14345]

theorem width_14346 : mW 14346 = 353637158845083 := by
  have hu : mW 14346 ≤ 353637158845083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14346 ≤ 353637158845082 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14346 : RowArithmetic 14346 (556685281123428588993/500000000000000000000000) (302740051190022094371653/500000000000000000000000) (214516089896381/31250000000000000000000) where
  r0 := (581974237867/1000000000000000000)
  k0 := (1803269545598179/500000000000000000)
  k6 := (571617119517781/50000000000000000)
  q := (33877426112383449489/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14346]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14346]

theorem width_14347 : mW 14347 = 353723443377774 := by
  have hu : mW 14347 ≤ 353723443377774 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14347 ≤ 353723443377773 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14347 : RowArithmetic 14347 (1113341592097391747427/1000000000000000000000000) (605469270666984237201021/1000000000000000000000000) (3431635039525029/500000000000000000000000) where
  r0 := (290956696331/500000000000000000)
  k0 := (90158763876549/25000000000000000)
  k6 := (11431943960662699/1000000000000000000)
  q := (42348258523816537219/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14347]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14347]

theorem width_14348 : mW 14348 = 353809742947067 := by
  have hu : mW 14348 ≤ 353809742947067 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14348 ≤ 353809742947066 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14348 : RowArithmetic 14348 (55665631435316950647/50000000000000000000000) (605458440454950605518927/1000000000000000000000000) (3431012798463377/500000000000000000000000) where
  r0 := (29092627903/50000000000000000)
  k0 := (3606162041927817/1000000000000000000)
  k6 := (2857886393156003/250000000000000000)
  q := (169398937422877596987/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14348]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14348]

theorem width_14349 : mW 14349 = 353896057554534 := by
  have hu : mW 14349 ≤ 353896057554534 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14349 ≤ 353896057554533 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14349 : RowArithmetic 14349 (69580229504477196103/62500000000000000000000) (605447611743610918847303/1000000000000000000000000) (214399419694113/31250000000000000000000) where
  r0 := (72723966757/125000000000000000)
  k0 := (3605973551782043/1000000000000000000)
  k6 := (11431147226232303/1000000000000000000)
  q := (84702420272386550029/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14349]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14349]

theorem width_14350 : mW 14350 = 353982387201747 := by
  have hu : mW 14350 ≤ 353982387201747 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14350 ≤ 353982387201746 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14350 : RowArithmetic 14350 (556627361095608545453/500000000000000000000000) (484349427626106316133/800000000000000000000) (6859537578802023/1000000000000000000000000) where
  r0 := (72716365081/125000000000000000)
  k0 := (901446271155511/250000000000000000)
  k6 := (5715374460740157/500000000000000000)
  q := (169410743460974162623/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14350]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14350]

theorem width_14351 : mW 14351 = 354068731890278 := by
  have hu : mW 14351 ≤ 354068731890278 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14351 ≤ 354068731890277 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14351 : RowArithmetic 14351 (139153222382877830987/125000000000000000000000) (605425958821684311814889/1000000000000000000000000) (1714573510648849/250000000000000000000000) where
  r0 := (116334023567/200000000000000000)
  k0 := (1802798320224163/500000000000000000)
  k6 := (1428793832295099/125000000000000000)
  q := (42354161542875571367/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14351]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14351]

theorem width_14352 : mW 14352 = 354155091621701 := by
  have hu : mW 14352 ≤ 354155091621701 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14352 ≤ 354155091621700 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14352 : RowArithmetic 14352 (139149605335623672019/125000000000000000000000) (605415134610433164057649/1000000000000000000000000) (6857050821489159/1000000000000000000000000) where
  r0 := (145402331403/250000000000000000)
  k0 := (1802704109624497/500000000000000000)
  k6 := (5714976218433243/500000000000000000)
  q := (84711274338189482817/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14352]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14352]

theorem width_14353 : mW 14353 = 354241466397586 := by
  have hu : mW 14353 ≤ 354241466397586 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14353 ≤ 354241466397585 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14353 : RowArithmetic 14353 (1113167913055057675173/1000000000000000000000000) (302702155949273726282641/500000000000000000000000) (3427903957690427/500000000000000000000000) where
  r0 := (290774271989/500000000000000000)
  k0 := (450652477628069/125000000000000000)
  k6 := (178586785265471/15625000000000000)
  q := (169428450975625696417/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14353]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14353]

theorem width_14354 : mW 14354 = 354327856219506 := by
  have hu : mW 14354 ≤ 354327856219506 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14354 ≤ 354327856219505 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14354 : RowArithmetic 14354 (1113138990171167229057/1000000000000000000000000) (151348372671423824877973/250000000000000000000000) (856820665521001/125000000000000000000000) where
  r0 := (58148777293/100000000000000000)
  k0 := (1802515722884651/500000000000000000)
  k6 := (5714578059362259/500000000000000000)
  q := (169434353069263967371/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14354]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14354]

theorem width_14355 : mW 14355 = 354414261089035 := by
  have hu : mW 14355 ≤ 354414261089035 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14355 ≤ 354414261089034 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14355 : RowArithmetic 14355 (556555037015629010503/500000000000000000000000) (151345667742886230168957/250000000000000000000000) (6853323047748169/1000000000000000000000000) where
  r0 := (290713506233/500000000000000000)
  k0 := (720968618696129/200000000000000000)
  k6 := (11428758022062361/1000000000000000000)
  q := (33888050991463052861/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14355]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14355]

theorem width_14356 : mW 14356 = 354500681007744 := by
  have hu : mW 14356 ≤ 354500681007744 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14356 ≤ 354500681007743 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14356 : RowArithmetic 14356 (139135145579159044599/125000000000000000000000) (37835740797235293926393/62500000000000000000000) (6852081086018987/1000000000000000000000000) where
  r0 := (290683131291/500000000000000000)
  k0 := (180232738207489/50000000000000000)
  k6 := (2857089991749107/250000000000000000)
  q := (169446156639801069287/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14356]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14356]

theorem width_14357 : mW 14357 = 354587115977206 := by
  have hu : mW 14357 ≤ 354587115977206 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14357 ≤ 354587115977205 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14357 : RowArithmetic 14357 (556526130987576166873/500000000000000000000000) (605361036038022963258189/1000000000000000000000000) (3425419719439057/500000000000000000000000) where
  r0 := (145326380819/250000000000000000)
  k0 := (720893291554821/200000000000000000)
  k6 := (2856990488379869/250000000000000000)
  q := (84726029058371430323/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14357]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14357]

theorem width_14358 : mW 14358 = 354673565998993 := by
  have hu : mW 14358 ≤ 354673565998993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14358 ≤ 354673565998992 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14358 : RowArithmetic 14358 (11130233660548413583/10000000000000000000000) (37834388801124270757971/62500000000000000000000) (6849598106223261/1000000000000000000000000) where
  r0 := (581244794547/1000000000000000000)
  k0 := (1802139087177059/500000000000000000)
  k6 := (11427563981624263/1000000000000000000)
  q := (21182244923520264121/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14358]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14358]

theorem width_14359 : mW 14359 = 354760031074679 := by
  have hu : mW 14359 ≤ 354760031074679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14359 ≤ 354760031074678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14359 : RowArithmetic 14359 (278248619217570657319/250000000000000000000000) (302669703547664703649803/500000000000000000000000) (1369671417590429/200000000000000000000000) where
  r0 := (58118407639/100000000000000000)
  k0 := (3604089913877913/1000000000000000000)
  k6 := (228543321026071/20000000000000000)
  q := (169463860454080297103/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14359]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14359]

theorem width_14360 : mW 14360 = 354846511205835 := by
  have hu : mW 14360 ≤ 354846511205835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14360 ≤ 354846511205834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14360 : RowArithmetic 14360 (1112965594419421663981/1000000000000000000000000) (605328594869714904079537/1000000000000000000000000) (342355819198129/50000000000000000000000) where
  r0 := (145280842201/250000000000000000)
  k0 := (720780335269197/200000000000000000)
  k6 := (5713384081275049/500000000000000000)
  q := (1059186008215743001/6250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14360]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14360]

theorem width_14361 : mW 14361 = 354933006394036 := by
  have hu : mW 14361 ≤ 354933006394036 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14361 ≤ 354933006394035 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14361 : RowArithmetic 14361 (1112936718700202761927/1000000000000000000000000) (605317784140813684665819/1000000000000000000000000) (6845875994152347/1000000000000000000000000) where
  r0 := (116212534357/200000000000000000)
  k0 := (1801856730874763/500000000000000000)
  k6 := (11426370315356671/1000000000000000000)
  q := (21184457746187415689/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14361]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14361]

theorem width_14362 : mW 14362 = 355019516640853 := by
  have hu : mW 14362 ≤ 355019516640853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14362 ≤ 355019516640852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14362 : RowArithmetic 14362 (1780652559536916871/1600000000000000000000) (605306974908294673420901/1000000000000000000000000) (1368927183683869/200000000000000000000000) where
  r0 := (581001985333/1000000000000000000)
  k0 := (3603525270092129/1000000000000000000)
  k6 := (5712986254858017/500000000000000000)
  q := (33896312483808618559/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14362]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14362]

theorem width_14363 : mW 14363 = 355106041947860 := by
  have hu : mW 14363 ≤ 355106041947860 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14363 ≤ 355106041947859 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14363 : RowArithmetic 14363 (139109873431059864987/125000000000000000000000) (605296167171826865115567/1000000000000000000000000) (3421698078330727/500000000000000000000000) where
  r0 := (580941309443/1000000000000000000)
  k0 := (3603337101361883/1000000000000000000)
  k6 := (2856393686405239/250000000000000000)
  q := (169487462663171637913/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14363]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14363]

theorem width_14364 : mW 14364 = 355192582316629 := by
  have hu : mW 14364 ≤ 355192582316629 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14364 ≤ 355192582316628 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14364 : RowArithmetic 14364 (1112850131911868607401/1000000000000000000000000) (302642680465539734486067/500000000000000000000000) (3421078354388319/500000000000000000000000) where
  r0 := (580880644113/1000000000000000000)
  k0 := (144125958222247/40000000000000000)
  k6 := (2856294255766051/250000000000000000)
  q := (16949336270190641303/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14364]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14364]

theorem width_14365 : mW 14365 = 355279137748733 := by
  have hu : mW 14365 ≤ 355279137748733 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14365 ≤ 355279137748732 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14365 : RowArithmetic 14365 (222564256619738124417/200000000000000000000000) (121054911237144329474649/200000000000000000000000) (3420458787331441/500000000000000000000000) where
  r0 := (580819989341/1000000000000000000)
  k0 := (1801480416336197/500000000000000000)
  k6 := (228495586840771/20000000000000000)
  q := (8474963126763443329/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14365]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14365]

theorem width_14366 : mW 14366 = 355365708245746 := by
  have hu : mW 14366 ≤ 355365708245746 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14366 ≤ 355365708245745 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14366 : RowArithmetic 14366 (556396220503446888023/500000000000000000000000) (605263752935422742125337/1000000000000000000000000) (6839678754218191/1000000000000000000000000) where
  r0 := (145189836281/250000000000000000)
  k0 := (3602772732704827/1000000000000000000)
  k6 := (11424381702536767/1000000000000000000)
  q := (169505162163280443263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14366]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14366]

theorem width_14367 : mW 14367 = 355452293809241 := by
  have hu : mW 14367 ≤ 355452293809241 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14367 ≤ 355452293809240 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14367 : RowArithmetic 14367 (44510544225377127433/40000000000000000000000) (302626475589926111243223/500000000000000000000000) (3419220123670317/500000000000000000000000) where
  r0 := (580698711459/1000000000000000000)
  k0 := (720516931129551/200000000000000000)
  k6 := (11423984104551627/1000000000000000000)
  q := (169511061585962584049/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14367]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14367]

theorem width_14368 : mW 14368 = 355538894440790 := by
  have hu : mW 14368 ≤ 355538894440790 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14368 ≤ 355538894440789 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14368 : RowArithmetic 14368 (17386480890300707359/15625000000000000000000) (121048430183735923087567/200000000000000000000000) (341860102696417/50000000000000000000000) where
  r0 := (72579761043/125000000000000000)
  k0 := (900599150374641/250000000000000000)
  k6 := (11423586548075909/1000000000000000000)
  q := (84758480401668363087/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14368]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14368]

theorem width_14369 : mW 14369 = 355625510141968 := by
  have hu : mW 14369 ≤ 355625510141968 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14369 ≤ 355625510141967 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14369 : RowArithmetic 14369 (1112705955039295740441/1000000000000000000000000) (37826959509473407763373/62500000000000000000000) (6835964173879419/1000000000000000000000000) where
  r0 := (580577475777/1000000000000000000)
  k0 := (3602208570254637/1000000000000000000)
  k6 := (11423189033102389/1000000000000000000)
  q := (169522859815424303147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14369]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14369]

theorem width_14370 : mW 14370 = 355712140914347 := by
  have hu : mW 14370 ≤ 355712140914347 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14370 ≤ 355712140914346 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14370 : RowArithmetic 14370 (111267713981253261229/100000000000000000000000) (15130513871955167308609/25000000000000000000000) (1708681651773021/250000000000000000000000) where
  r0 := (116103374751/200000000000000000)
  k0 := (3602020561910253/1000000000000000000)
  k6 := (11422791559623847/1000000000000000000)
  q := (169528758622246744747/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14370]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14370]

theorem width_14371 : mW 14371 = 355798786759500 := by
  have hu : mW 14371 ≤ 355798786759500 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14371 ≤ 355798786759499 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14371 : RowArithmetic 14371 (139081041412113649961/125000000000000000000000) (605209759098245982417193/1000000000000000000000000) (854186169183071/125000000000000000000000) where
  r0 := (290228141137/500000000000000000)
  k0 := (900458144114147/250000000000000000)
  k6 := (1427799265954133/125000000000000000)
  q := (169534657223825477023/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14371]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14371]

theorem width_14372 : mW 14372 = 355885447679001 := by
  have hu : mW 14372 ≤ 355885447679001 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14372 ≤ 355885447679000 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14372 : RowArithmetic 14372 (1112619529490379111507/1000000000000000000000000) (15129974120284058377541/25000000000000000000000) (3416126206447563/500000000000000000000000) where
  r0 := (290197850667/500000000000000000)
  k0 := (3601644613897227/1000000000000000000)
  k6 := (1427749592140353/125000000000000000)
  q := (1695405556201819223/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14372]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14372]

theorem width_14373 : mW 14373 = 355972123674424 := by
  have hu : mW 14373 ≤ 355972123674424 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14373 ≤ 355972123674423 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14373 : RowArithmetic 14373 (55629536719544837759/50000000000000000000000) (60518817201722571709807/100000000000000000000000) (853876973160257/125000000000000000000000) where
  r0 := (58033513093/100000000000000000)
  k0 := (3601456674220239/1000000000000000000)
  k6 := (11421599388085911/1000000000000000000)
  q := (6781858152453499967/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14373]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14373]

theorem width_14374 : mW 14374 = 356058814747342 := by
  have hu : mW 14374 ≤ 356058814747342 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14374 ≤ 356058814747341 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14374 : RowArithmetic 14374 (4345945101548507181/3906250000000000000000) (302588690357753164168893/500000000000000000000000) (1365955894104743/200000000000000000000000) where
  r0 := (580274571061/1000000000000000000)
  k0 := (450158594678263/125000000000000000)
  k6 := (1427650260064389/125000000000000000)
  q := (84776175898656811259/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14374]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14374]

theorem width_14375 : mW 14375 = 356145520899328 := by
  have hu : mW 14375 ≤ 356145520899328 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14375 ≤ 356145520899327 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14375 : RowArithmetic 14375 (222506632860979773109/200000000000000000000000) (302583295452937206100101/500000000000000000000000) (6828543468518503/1000000000000000000000000) where
  r0 := (23208560869/40000000000000000)
  k0 := (3601080863512197/1000000000000000000)
  k6 := (2284160962880643/200000000000000000)
  q := (169558249578131703477/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14375]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14375]

theorem width_14376 : mW 14376 = 356232242131957 := by
  have hu : mW 14376 ≤ 356232242131957 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14376 ≤ 356232242131956 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14376 : RowArithmetic 14376 (556252194657148067333/500000000000000000000000) (121031160517600052246271/200000000000000000000000) (341365388958241/50000000000000000000000) where
  r0 := (580153482917/1000000000000000000)
  k0 := (450111624058323/125000000000000000)
  k6 := (11420407589743011/1000000000000000000)
  q := (42391036788453287369/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14376]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14376]

theorem width_14377 : mW 14377 = 356318978446801 := by
  have hu : mW 14377 ≤ 356318978446801 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14377 ≤ 356318978446800 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14377 : RowArithmetic 14377 (278118905255642061399/250000000000000000000000) (121029003152310859054989/200000000000000000000000) (426629525147573/62500000000000000000000) where
  r0 := (145023238659/250000000000000000)
  k0 := (3600705144289741/1000000000000000000)
  k6 := (2855002601631823/250000000000000000)
  q := (33914008904875872843/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14377]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14377]

theorem width_14378 : mW 14378 = 356405729845434 := by
  have hu : mW 14378 ≤ 356405729845434 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14378 ≤ 356405729845433 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14378 : RowArithmetic 14378 (1112446859427673590719/1000000000000000000000000) (605134230426207078804249/1000000000000000000000000) (136496746760121/20000000000000000000000) where
  r0 := (7250405461/12500000000000000)
  k0 := (3600517318979039/1000000000000000000)
  k6 := (228392265294977/20000000000000000)
  q := (169575941689851747673/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14378]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14378]

theorem width_14379 : mW 14379 = 356492496329431 := by
  have hu : mW 14379 ≤ 356492496329431 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14379 ≤ 356492496329430 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14379 : RowArithmetic 14379 (69526131532973178597/62500000000000000000000) (75640430822703658582521/125000000000000000000000) (6823602585997993/1000000000000000000000000) where
  r0 := (115994385929/200000000000000000)
  k0 := (3600329516525641/1000000000000000000)
  k6 := (5709608082200241/500000000000000000)
  q := (42395459662562924027/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14379]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14379]

theorem width_14380 : mW 14380 = 356579277900365 := by
  have hu : mW 14380 ≤ 356579277900365 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14380 ≤ 356579277900364 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14380 : RowArithmetic 14380 (1112389356320220531803/1000000000000000000000000) (75639083028436450736671/125000000000000000000000) (3411184073117801/500000000000000000000000) where
  r0 := (57991143293/100000000000000000)
  k0 := (180007086846501/50000000000000000)
  k6 := (1427352388184373/125000000000000000)
  q := (169587735405600602059/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14380]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14380]

theorem width_14381 : mW 14381 = 356666074559810 := by
  have hu : mW 14381 ≤ 356666074559810 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14381 ≤ 356666074559809 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14381 : RowArithmetic 14381 (556180307401791696553/500000000000000000000000) (302550941681732438095117/500000000000000000000000) (6821134018617503/1000000000000000000000000) where
  r0 := (579850946731/1000000000000000000)
  k0 := (1799976990091669/500000000000000000)
  k6 := (2854605521991289/250000000000000000)
  q := (21199203994489981793/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14381]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14381]

theorem width_14382 : mW 14382 = 356752886309340 := by
  have hu : mW 14382 ≤ 356752886309340 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14382 ≤ 356752886309339 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14382 : RowArithmetic 14382 (556165939987810508023/500000000000000000000000) (302545551994610017596263/500000000000000000000000) (6819900203042367/1000000000000000000000000) where
  r0 := (289895235523/500000000000000000)
  k0 := (3599766246282959/1000000000000000000)
  k6 := (11418025111863797/1000000000000000000)
  q := (10599970518826927379/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14382]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14382]

theorem width_14383 : mW 14383 = 356839713150528 := by
  have hu : mW 14383 ≤ 356839713150528 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14383 ≤ 356839713150527 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14383 : RowArithmetic 14383 (556151575917148134981/500000000000000000000000) (605080326104428105460563/1000000000000000000000000) (6818666699408921/1000000000000000000000000) where
  r0 := (36233125367/62500000000000000)
  k0 := (719915707044629/200000000000000000)
  k6 := (178400440268183/15625000000000000)
  q := (169605424441554934603/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14383]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14383]

theorem width_14384 : mW 14384 = 356926555084950 := by
  have hu : mW 14384 ≤ 356926555084950 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14384 ≤ 356926555084949 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14384 : RowArithmetic 14384 (556137215188785658759/500000000000000000000000) (151267387427190053953619/250000000000000000000000) (6817433507615879/1000000000000000000000000) where
  r0 := (72458693901/125000000000000000)
  k0 := (719878169400873/200000000000000000)
  k6 := (11417231283857703/1000000000000000000)
  q := (169611320376913521627/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14384]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14384]

theorem width_14385 : mW 14385 = 357013412114178 := by
  have hu : mW 14385 ≤ 357013412114178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14385 ≤ 357013412114177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14385 : RowArithmetic 14385 (1112245715603411115957/1000000000000000000000000) (302529387400943823817109/500000000000000000000000) (6816200627562071/1000000000000000000000000) where
  r0 := (579609107049/1000000000000000000)
  k0 := (3599203181614669/1000000000000000000)
  k6 := (713552151996161/62500000000000000)
  q := (169617216107327973089/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14385]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14385]

theorem width_14386 : mW 14386 = 357100284239788 := by
  have hu : mW 14386 ≤ 357100284239788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14386 ≤ 357100284239787 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14386 : RowArithmetic 14386 (278054251877444853963/250000000000000000000000) (151262000345870419444539/250000000000000000000000) (6814968059146293/1000000000000000000000000) where
  r0 := (115909734679/200000000000000000)
  k0 := (1799507769528813/500000000000000000)
  k6 := (570821881069957/50000000000000000)
  q := (84811555816409829613/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14386]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14386]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14312 then ⟨(557179791686063933799/500000000000000000000000), (151462319028649760176587/250000000000000000000000), (6907026460924519/1000000000000000000000000)⟩ else
  if n = 14313 then ⟨(557165191101512465379/500000000000000000000000), (605838393168156569167891/1000000000000000000000000), (6905770874543687/1000000000000000000000000)⟩ else
  if n = 14314 then ⟨(111430118786297323993/100000000000000000000000), (121165502346820308850597/200000000000000000000000), (1726128901797179/250000000000000000000000)⟩ else
  if n = 14315 then ⟨(1114272000349882348481/1000000000000000000000000), (605816631812098233326057/1000000000000000000000000), (138065213175111/20000000000000000000000)⟩ else
  if n = 14316 then ⟨(1114242819661662114313/1000000000000000000000000), (605805753401810791823103/1000000000000000000000000), (862750753642519/125000000000000000000000)⟩ else
  if n = 14317 then ⟨(111421364579622372807/100000000000000000000000), (605794876502903706910607/1000000000000000000000000), (6900751718238549/1000000000000000000000000)⟩ else
  if n = 14318 then ⟨(557092239375739342261/500000000000000000000000), (30289200055752068487303/50000000000000000000000), (6899497725946791/1000000000000000000000000)⟩ else
  if n = 14319 then ⟨(222831063705068064661/200000000000000000000000), (302886563618944203001143/500000000000000000000000), (6898244052161009/1000000000000000000000000)⟩ else
  if n = 14320 then ⟨(1114126165115720747449/1000000000000000000000000), (605762254871109417415983/1000000000000000000000000), (6896990696777299/1000000000000000000000000)⟩ else
  if n = 14321 then ⟨(1114097018520535443719/1000000000000000000000000), (151437846003592318205097/250000000000000000000000), (6895737659691897/1000000000000000000000000)⟩ else
  if n = 14322 then ⟨(1114067878737698662283/1000000000000000000000000), (121148102933466559334793/200000000000000000000000), (6894484940801001/1000000000000000000000000)⟩ else
  if n = 14323 then ⟨(1114038745765125983153/1000000000000000000000000), (605729646829665001638767/1000000000000000000000000), (55145860320007/8000000000000000000000)⟩ else
  if n = 14324 then ⟨(44560384784029372589/40000000000000000000000), (605718780501030978941853/1000000000000000000000000), (3445990228593921/500000000000000000000000)⟩ else
  if n = 14325 then ⟨(1113980500242440868093/1000000000000000000000000), (302853957840547937554069/500000000000000000000000), (6890728692258247/1000000000000000000000000)⟩ else
  if n = 14326 then ⟨(69621961730510229349/62500000000000000000000), (605697052369525012378471/1000000000000000000000000), (5382404097741/781250000000000000000)⟩ else
  if n = 14327 then ⟨(1113922281935821560347/1000000000000000000000000), (302843095282991890921063/500000000000000000000000), (1722056528908743/250000000000000000000000)⟩ else
  if n = 14328 then ⟨(1113893182983334195941/1000000000000000000000000), (302837665135068840378281/500000000000000000000000), (1721743825933549/250000000000000000000000)⟩ else
  if n = 14329 then ⟨(1113864090828622045927/1000000000000000000000000), (605664471481652294336621/1000000000000000000000000), (1721431202325667/250000000000000000000000)⟩ else
  if n = 14330 then ⟨(111383500546960690453/100000000000000000000000), (302826807100096659194229/500000000000000000000000), (1376894926447393/200000000000000000000000)⟩ else
  if n = 14331 then ⟨(556902963452104922853/500000000000000000000000), (605642758425426554514821/1000000000000000000000000), (430201548277103/62500000000000000000000)⟩ else
  if n = 14332 then ⟨(111377685513035428983/100000000000000000000000), (605631904157017912962183/1000000000000000000000000), (3440987614894689/500000000000000000000000)⟩ else
  if n = 14333 then ⟨(111374779014596344789/100000000000000000000000), (37851315712164584540413/62500000000000000000000), (6880726004200821/1000000000000000000000000)⟩ else
  if n = 14334 then ⟨(69607420746810147759/62500000000000000000000), (302805100068969510366199/500000000000000000000000), (3439738547782361/500000000000000000000000)⟩ else
  if n = 14335 then ⟨(111368968053727536343/100000000000000000000000), (605599350386601114291489/1000000000000000000000000), (1719557125944453/250000000000000000000000)⟩ else
  if n = 14336 then ⟨(1113660635908829112873/1000000000000000000000000), (605588502140285936114527/1000000000000000000000000), (6876980228736919/1000000000000000000000000)⟩ else
  if n = 14337 then ⟨(278407899515387517557/250000000000000000000000), (605577655398659896287483/1000000000000000000000000), (3437866135169439/500000000000000000000000)⟩ else
  if n = 14338 then ⟨(1113602566993365504383/1000000000000000000000000), (75695851270173690149059/125000000000000000000000), (1718621157120141/250000000000000000000000)⟩ else
  if n = 14339 then ⟨(556786771351102002081/500000000000000000000000), (302777983214070672554037/500000000000000000000000), (3436618651529457/500000000000000000000000)⟩ else
  if n = 14340 then ⟨(1113544525185994458871/1000000000000000000000000), (605545124198582197686841/1000000000000000000000000), (858998786746361/125000000000000000000000)⟩ else
  if n = 14341 then ⟨(1113515514442667076519/1000000000000000000000000), (302767141736189407190913/500000000000000000000000), (1374148720222701/200000000000000000000000)⟩ else
  if n = 14342 then ⟨(1113486510470151856597/1000000000000000000000000), (605523444249198110558683/1000000000000000000000000), (429343576523987/62500000000000000000000)⟩ else
  if n = 14343 then ⟨(222691502653276125057/200000000000000000000000), (37844537908044196598639/62500000000000000000000), (6868251163678851/1000000000000000000000000)⟩ else
  if n = 14344 then ⟨(69589282676830344277/62500000000000000000000), (302750885155286494348459/500000000000000000000000), (6867005418895811/1000000000000000000000000)⟩ else
  if n = 14345 then ⟨(556699769578399974067/500000000000000000000000), (605490935594462892793463/1000000000000000000000000), (6865759989931861/1000000000000000000000000)⟩ else
  if n = 14346 then ⟨(556685281123428588993/500000000000000000000000), (302740051190022094371653/500000000000000000000000), (214516089896381/31250000000000000000000)⟩ else
  if n = 14347 then ⟨(1113341592097391747427/1000000000000000000000000), (605469270666984237201021/1000000000000000000000000), (3431635039525029/500000000000000000000000)⟩ else
  if n = 14348 then ⟨(55665631435316950647/50000000000000000000000), (605458440454950605518927/1000000000000000000000000), (3431012798463377/500000000000000000000000)⟩ else
  if n = 14349 then ⟨(69580229504477196103/62500000000000000000000), (605447611743610918847303/1000000000000000000000000), (214399419694113/31250000000000000000000)⟩ else
  if n = 14350 then ⟨(556627361095608545453/500000000000000000000000), (484349427626106316133/800000000000000000000), (6859537578802023/1000000000000000000000000)⟩ else
  if n = 14351 then ⟨(139153222382877830987/125000000000000000000000), (605425958821684311814889/1000000000000000000000000), (1714573510648849/250000000000000000000000)⟩ else
  if n = 14352 then ⟨(139149605335623672019/125000000000000000000000), (605415134610433164057649/1000000000000000000000000), (6857050821489159/1000000000000000000000000)⟩ else
  if n = 14353 then ⟨(1113167913055057675173/1000000000000000000000000), (302702155949273726282641/500000000000000000000000), (3427903957690427/500000000000000000000000)⟩ else
  if n = 14354 then ⟨(1113138990171167229057/1000000000000000000000000), (151348372671423824877973/250000000000000000000000), (856820665521001/125000000000000000000000)⟩ else
  if n = 14355 then ⟨(556555037015629010503/500000000000000000000000), (151345667742886230168957/250000000000000000000000), (6853323047748169/1000000000000000000000000)⟩ else
  if n = 14356 then ⟨(139135145579159044599/125000000000000000000000), (37835740797235293926393/62500000000000000000000), (6852081086018987/1000000000000000000000000)⟩ else
  if n = 14357 then ⟨(556526130987576166873/500000000000000000000000), (605361036038022963258189/1000000000000000000000000), (3425419719439057/500000000000000000000000)⟩ else
  if n = 14358 then ⟨(11130233660548413583/10000000000000000000000), (37834388801124270757971/62500000000000000000000), (6849598106223261/1000000000000000000000000)⟩ else
  if n = 14359 then ⟨(278248619217570657319/250000000000000000000000), (302669703547664703649803/500000000000000000000000), (1369671417590429/200000000000000000000000)⟩ else
  if n = 14360 then ⟨(1112965594419421663981/1000000000000000000000000), (605328594869714904079537/1000000000000000000000000), (342355819198129/50000000000000000000000)⟩ else
  if n = 14361 then ⟨(1112936718700202761927/1000000000000000000000000), (605317784140813684665819/1000000000000000000000000), (6845875994152347/1000000000000000000000000)⟩ else
  if n = 14362 then ⟨(1780652559536916871/1600000000000000000000), (605306974908294673420901/1000000000000000000000000), (1368927183683869/200000000000000000000000)⟩ else
  if n = 14363 then ⟨(139109873431059864987/125000000000000000000000), (605296167171826865115567/1000000000000000000000000), (3421698078330727/500000000000000000000000)⟩ else
  if n = 14364 then ⟨(1112850131911868607401/1000000000000000000000000), (302642680465539734486067/500000000000000000000000), (3421078354388319/500000000000000000000000)⟩ else
  if n = 14365 then ⟨(222564256619738124417/200000000000000000000000), (121054911237144329474649/200000000000000000000000), (3420458787331441/500000000000000000000000)⟩ else
  if n = 14366 then ⟨(556396220503446888023/500000000000000000000000), (605263752935422742125337/1000000000000000000000000), (6839678754218191/1000000000000000000000000)⟩ else
  if n = 14367 then ⟨(44510544225377127433/40000000000000000000000), (302626475589926111243223/500000000000000000000000), (3419220123670317/500000000000000000000000)⟩ else
  if n = 14368 then ⟨(17386480890300707359/15625000000000000000000), (121048430183735923087567/200000000000000000000000), (341860102696417/50000000000000000000000)⟩ else
  if n = 14369 then ⟨(1112705955039295740441/1000000000000000000000000), (37826959509473407763373/62500000000000000000000), (6835964173879419/1000000000000000000000000)⟩ else
  if n = 14370 then ⟨(111267713981253261229/100000000000000000000000), (15130513871955167308609/25000000000000000000000), (1708681651773021/250000000000000000000000)⟩ else
  if n = 14371 then ⟨(139081041412113649961/125000000000000000000000), (605209759098245982417193/1000000000000000000000000), (854186169183071/125000000000000000000000)⟩ else
  if n = 14372 then ⟨(1112619529490379111507/1000000000000000000000000), (15129974120284058377541/25000000000000000000000), (3416126206447563/500000000000000000000000)⟩ else
  if n = 14373 then ⟨(55629536719544837759/50000000000000000000000), (60518817201722571709807/100000000000000000000000), (853876973160257/125000000000000000000000)⟩ else
  if n = 14374 then ⟨(4345945101548507181/3906250000000000000000), (302588690357753164168893/500000000000000000000000), (1365955894104743/200000000000000000000000)⟩ else
  if n = 14375 then ⟨(222506632860979773109/200000000000000000000000), (302583295452937206100101/500000000000000000000000), (6828543468518503/1000000000000000000000000)⟩ else
  if n = 14376 then ⟨(556252194657148067333/500000000000000000000000), (121031160517600052246271/200000000000000000000000), (341365388958241/50000000000000000000000)⟩ else
  if n = 14377 then ⟨(278118905255642061399/250000000000000000000000), (121029003152310859054989/200000000000000000000000), (426629525147573/62500000000000000000000)⟩ else
  if n = 14378 then ⟨(1112446859427673590719/1000000000000000000000000), (605134230426207078804249/1000000000000000000000000), (136496746760121/20000000000000000000000)⟩ else
  if n = 14379 then ⟨(69526131532973178597/62500000000000000000000), (75640430822703658582521/125000000000000000000000), (6823602585997993/1000000000000000000000000)⟩ else
  if n = 14380 then ⟨(1112389356320220531803/1000000000000000000000000), (75639083028436450736671/125000000000000000000000), (3411184073117801/500000000000000000000000)⟩ else
  if n = 14381 then ⟨(556180307401791696553/500000000000000000000000), (302550941681732438095117/500000000000000000000000), (6821134018617503/1000000000000000000000000)⟩ else
  if n = 14382 then ⟨(556165939987810508023/500000000000000000000000), (302545551994610017596263/500000000000000000000000), (6819900203042367/1000000000000000000000000)⟩ else
  if n = 14383 then ⟨(556151575917148134981/500000000000000000000000), (605080326104428105460563/1000000000000000000000000), (6818666699408921/1000000000000000000000000)⟩ else
  if n = 14384 then ⟨(556137215188785658759/500000000000000000000000), (151267387427190053953619/250000000000000000000000), (6817433507615879/1000000000000000000000000)⟩ else
  if n = 14385 then ⟨(1112245715603411115957/1000000000000000000000000), (302529387400943823817109/500000000000000000000000), (6816200627562071/1000000000000000000000000)⟩ else
  ⟨(278054251877444853963/250000000000000000000000), (151262000345870419444539/250000000000000000000000), (6814968059146293/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14312 ≤ n) (hb : n ≤ 14386) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14312
  · exact row_14313
  · exact row_14314
  · exact row_14315
  · exact row_14316
  · exact row_14317
  · exact row_14318
  · exact row_14319
  · exact row_14320
  · exact row_14321
  · exact row_14322
  · exact row_14323
  · exact row_14324
  · exact row_14325
  · exact row_14326
  · exact row_14327
  · exact row_14328
  · exact row_14329
  · exact row_14330
  · exact row_14331
  · exact row_14332
  · exact row_14333
  · exact row_14334
  · exact row_14335
  · exact row_14336
  · exact row_14337
  · exact row_14338
  · exact row_14339
  · exact row_14340
  · exact row_14341
  · exact row_14342
  · exact row_14343
  · exact row_14344
  · exact row_14345
  · exact row_14346
  · exact row_14347
  · exact row_14348
  · exact row_14349
  · exact row_14350
  · exact row_14351
  · exact row_14352
  · exact row_14353
  · exact row_14354
  · exact row_14355
  · exact row_14356
  · exact row_14357
  · exact row_14358
  · exact row_14359
  · exact row_14360
  · exact row_14361
  · exact row_14362
  · exact row_14363
  · exact row_14364
  · exact row_14365
  · exact row_14366
  · exact row_14367
  · exact row_14368
  · exact row_14369
  · exact row_14370
  · exact row_14371
  · exact row_14372
  · exact row_14373
  · exact row_14374
  · exact row_14375
  · exact row_14376
  · exact row_14377
  · exact row_14378
  · exact row_14379
  · exact row_14380
  · exact row_14381
  · exact row_14382
  · exact row_14383
  · exact row_14384
  · exact row_14385
  · exact row_14386

end BstLean.Part271.R3.Rows14312
