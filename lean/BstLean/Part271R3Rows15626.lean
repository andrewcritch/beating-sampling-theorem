import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15626–15700. -/
namespace BstLean.Part271.R3.Rows15626
open Real BstLean.Part130 BstLean.Part227

theorem width_15626 : mW 15626 = 476943978271758 := by
  have hu : mW 15626 ≤ 476943978271758 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15626 ≤ 476943978271757 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15626 : RowArithmetic 15626 (33786842960063752789/31250000000000000000000) (592738522794691929857683/1000000000000000000000000) (687211313730833/125000000000000000000000) where
  r0 := (127987712983/250000000000000000)
  k0 := (1691308778777563/500000000000000000)
  k6 := (10954100624491659/1000000000000000000)
  q := (176782352060379601683/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15626]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15626]

theorem width_15627 : mW 15627 = 477050815431876 := by
  have hu : mW 15627 ≤ 477050815431876 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15627 ≤ 477050815431875 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15627 : RowArithmetic 15627 (1081157203077768925191/1000000000000000000000000) (592729371666030720422963/1000000000000000000000000) (5496777877976743/1000000000000000000000000) where
  r0 := (511901711727/1000000000000000000)
  k0 := (3382455211395777/1000000000000000000)
  k6 := (5476875066263343/500000000000000000)
  q := (35357601728624072503/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15627]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15627]

theorem width_15628 : mW 15628 = 477157669685118 := by
  have hu : mW 15628 ≤ 477157669685118 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15628 ≤ 477157669685117 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15628 : RowArithmetic 15628 (1081135436083098614109/1000000000000000000000000) (592720221683814430034051/1000000000000000000000000) (2747932728954857/500000000000000000000000) where
  r0 := (255926289691/500000000000000000)
  k0 := (1691146441706609/500000000000000000)
  k6 := (547669983710151/50000000000000000)
  q := (35358733008975307457/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15628]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15628]

theorem width_15629 : mW 15629 = 477264541033126 := by
  have hu : mW 15629 ≤ 477264541033126 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15629 ≤ 477264541033125 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15629 : RowArithmetic 15629 (540556836868364254149/500000000000000000000000) (118542214569562693793983/200000000000000000000000) (5494953249582447/1000000000000000000000000) where
  r0 := (31987715931/62500000000000000)
  k0 := (1691065286803381/500000000000000000)
  k6 := (10953049249515281/1000000000000000000)
  q := (176799321265665496899/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15629]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15629]

theorem width_15630 : mW 15630 = 477371429477541 := by
  have hu : mW 15630 ≤ 477371429477541 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15630 ≤ 477371429477540 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15630 : RowArithmetic 15630 (1081091916037358734323/1000000000000000000000000) (592701925157798352935593/1000000000000000000000000) (2747020626465923/500000000000000000000000) where
  r0 := (127938584567/250000000000000000)
  k0 := (84549207049393/25000000000000000)
  k6 := (1369087357307261/125000000000000000)
  q := (35360995461100921897/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15630]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15630]

theorem width_15631 : mW 15631 = 477478335020003 := by
  have hu : mW 15631 ≤ 477478335020003 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15631 ≤ 477478335020002 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15631 : RowArithmetic 15631 (1081070162983690192221/1000000000000000000000000) (592692778613539563284631/1000000000000000000000000) (109862589357897/20000000000000000000000) where
  r0 := (102341045899/200000000000000000)
  k0 := (3381806008512797/1000000000000000000)
  k6 := (10952348501026063/1000000000000000000)
  q := (35362126632882248079/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15631]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15631]

theorem width_15632 : mW 15632 = 477585257662154 := by
  have hu : mW 15632 ≤ 477585257662154 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15632 ≤ 477585257662153 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15632 : RowArithmetic 15632 (1081048414574423630489/1000000000000000000000000) (118536726642961537069067/200000000000000000000000) (1373054473602099/250000000000000000000000) where
  r0 := (7994627009/15625000000000000)
  k0 := (1690821876608651/500000000000000000)
  k6 := (10951998177213827/1000000000000000000)
  q := (88408144421201376101/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15632]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15632]

theorem width_15633 : mW 15633 = 477692197405634 := by
  have hu : mW 15633 ≤ 477692197405634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15633 ≤ 477692197405633 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15633 : RowArithmetic 15633 (540513335404130439431/500000000000000000000000) (4741395911690987574053/8000000000000000000000) (42900832284449/7812500000000000000000) where
  r0 := (511607035509/1000000000000000000)
  k0 := (3381481516085243/1000000000000000000)
  k6 := (2190329577403201/200000000000000000)
  q := (176821944339496504701/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15633]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15633]

theorem width_15634 : mW 15634 = 477799154252085 := by
  have hu : mW 15634 ≤ 477799154252085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15634 ≤ 477799154252084 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15634 : RowArithmetic 15634 (1081004931683903615557/1000000000000000000000000) (592665345853007549527007/1000000000000000000000000) (5490395381835063/1000000000000000000000000) where
  r0 := (127889487573/250000000000000000)
  k0 := (3381319297112623/1000000000000000000)
  k6 := (10951297630427221/1000000000000000000)
  q := (88413799827854927457/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15634]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15634]

theorem width_15635 : mW 15635 = 477906128203147 := by
  have hu : mW 15635 ≤ 477906128203147 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15635 ≤ 477906128203146 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15635 : RowArithmetic 15635 (1080983197200054599143/1000000000000000000000000) (296328101944740362283239/500000000000000000000000) (2744742221311101/500000000000000000000000) where
  r0 := (511508872923/1000000000000000000)
  k0 := (1690578548147723/500000000000000000)
  k6 := (109509474074421/10000000000000000)
  q := (88416627395530078543/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15635]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15635]

theorem width_15636 : mW 15636 = 478013119260462 := by
  have hu : mW 15636 ≤ 478013119260462 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15636 ≤ 478013119260461 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15636 : RowArithmetic 15636 (1080961467355416436703/1000000000000000000000000) (74080882883820487068637/125000000000000000000000) (2744286857353961/500000000000000000000000) where
  r0 := (511459803401/1000000000000000000)
  k0 := (169049745681651/50000000000000000)
  k6 := (1095059721805527/100000000000000000)
  q := (88419454872782381343/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15636]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15636]

theorem width_15637 : mW 15637 = 478120127425671 := by
  have hu : mW 15637 ≤ 478120127425671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15637 ≤ 478120127425670 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15637 : RowArithmetic 15637 (43237589685947700291/40000000000000000000000) (592637923396027911556531/1000000000000000000000000) (1371915799507323/250000000000000000000000) where
  r0 := (20456429669/40000000000000000)
  k0 := (845208187281163/250000000000000000)
  k6 := (136878088278267/12500000000000000)
  q := (17684456451924102041/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15637]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15637]

theorem width_15638 : mW 15638 = 478227152700415 := by
  have hu : mW 15638 ≤ 478227152700415 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15638 ≤ 478227152700414 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15638 : RowArithmetic 15638 (540459010789293326839/500000000000000000000000) (592628784865643832986639/1000000000000000000000000) (1371688223130851/250000000000000000000000) where
  r0 := (511361687891/1000000000000000000)
  k0 := (3380670602759733/1000000000000000000)
  k6 := (10949896940054999/1000000000000000000)
  q := (176850219112106276181/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15638]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15638]

theorem width_15639 : mW 15639 = 478334195086335 := by
  have hu : mW 15639 ≤ 478334195086335 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15639 ≤ 478334195086334 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15639 : RowArithmetic 15639 (540448152821901591149/500000000000000000000000) (592619647479182620549733/1000000000000000000000000) (1371460699531843/250000000000000000000000) where
  r0 := (511312641899/1000000000000000000)
  k0 := (422563559317609/125000000000000000)
  k6 := (342173339107213/31250000000000000)
  q := (176855873524177873147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15639]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15639]

theorem width_15640 : mW 15640 = 478441254585072 := by
  have hu : mW 15640 ≤ 478441254585072 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15640 ≤ 478441254585071 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15640 : RowArithmetic 15640 (1080874594343046862871/1000000000000000000000000) (592610511236415446876987/1000000000000000000000000) (1096986582955667/200000000000000000000000) where
  r0 := (511263603747/1000000000000000000)
  k0 := (338034636446407/100000000000000000)
  k6 := (5474598398191723/500000000000000000)
  q := (88430763877736575843/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15640]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15640]

theorem width_15641 : mW 15641 = 478548331198269 := by
  have hu : mW 15641 ≤ 478548331198269 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15641 ≤ 478548331198268 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15641 : RowArithmetic 15641 (43234115507000892567/40000000000000000000000) (296300688068556716219229/500000000000000000000000) (5484023242413433/1000000000000000000000000) where
  r0 := (63901821679/125000000000000000)
  k0 := (1690092136261009/500000000000000000)
  k6 := (17107573085793/1562500000000000)
  q := (176867181806009449403/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15641]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15641]

theorem width_15642 : mW 15642 = 478655424927566 := by
  have hu : mW 15642 ≤ 478655424927566 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15642 ≤ 478655424927565 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15642 : RowArithmetic 15642 (540415592819217769813/500000000000000000000000) (23703689687241911238877/40000000000000000000000) (2741556890484931/500000000000000000000000) where
  r0 := (255582775477/500000000000000000)
  k0 := (135200887948693/40000000000000000)
  k6 := (10948496786997673/1000000000000000000)
  q := (176872835675804101131/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15642]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15642]

theorem width_15643 : mW 15643 = 478762535774605 := by
  have hu : mW 15643 ≤ 478762535774605 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15643 ≤ 478762535774604 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15643 : RowArithmetic 15643 (270202372057998097813/250000000000000000000000) (148145777341997462935823/250000000000000000000000) (5482204530384821/1000000000000000000000000) where
  r0 := (51111653631/100000000000000000)
  k0 := (3379860143042683/1000000000000000000)
  k6 := (547407341632427/50000000000000000)
  q := (35375697872974887787/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15643]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15643]

theorem width_15644 : mW 15644 = 478869663741028 := by
  have hu : mW 15644 ≤ 478869663741028 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15644 ≤ 478869663741027 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15644 : RowArithmetic 15644 (1080787795454399184033/1000000000000000000000000) (118514795539542185345523/200000000000000000000000) (5481295490595529/1000000000000000000000000) where
  r0 := (511067529499/1000000000000000000)
  k0 := (3379698105497391/1000000000000000000)
  k6 := (5473898455927379/500000000000000000)
  q := (176884142873237792107/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15644]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15644]

theorem width_15645 : mW 15645 = 478976808828475 := by
  have hu : mW 15645 ≤ 478976808828475 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15645 ≤ 478976808828474 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15645 : RowArithmetic 15645 (1080766107304363308869/1000000000000000000000000) (148141211792495624093897/250000000000000000000000) (1096077332307851/200000000000000000000000) where
  r0 := (511018530519/1000000000000000000)
  k0 := (675907217215489/200000000000000000)
  k6 := (5473723512305483/500000000000000000)
  q := (44222449050227871793/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15645]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15645]

theorem width_15646 : mW 15646 = 479083971038590 := by
  have hu : mW 15646 ≤ 479083971038590 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15646 ≤ 479083971038589 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15646 : RowArithmetic 15646 (540372211890295696181/500000000000000000000000) (59255571778457597685299/100000000000000000000000) (5479478043153243/1000000000000000000000000) where
  r0 := (63871192421/125000000000000000)
  k0 := (3379374084778837/1000000000000000000)
  k6 := (10947097170911801/1000000000000000000)
  q := (35379089869582569577/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15646]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15646]

theorem width_15647 : mW 15647 = 479191150373013 := by
  have hu : mW 15647 ≤ 479191150373013 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15647 ≤ 479191150373012 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15647 : RowArithmetic 15647 (1080722744881791749789/1000000000000000000000000) (592546589541262978021729/1000000000000000000000000) (684821204421851/125000000000000000000000) where
  r0 := (102184111209/200000000000000000)
  k0 := (844803025400217/250000000000000000)
  k6 := (2189349470150381/200000000000000000)
  q := (35380220462851839047/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15647]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15647]

theorem width_15648 : mW 15648 = 479298346833386 := by
  have hu : mW 15648 ≤ 479298346833386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15648 ≤ 479298346833385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15648 : RowArithmetic 15648 (135087633825834068139/125000000000000000000000) (592537462439815025126797/1000000000000000000000000) (5477661438141263/1000000000000000000000000) where
  r0 := (510871580547/1000000000000000000)
  k0 := (3379050136536221/1000000000000000000)
  k6 := (10946397564125919/1000000000000000000)
  q := (176906755099967847441/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15648]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15648]

theorem width_15649 : mW 15649 = 479405560421351 := by
  have hu : mW 15649 ≤ 479405560421351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15649 ≤ 479405560421350 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15649 : RowArithmetic 15649 (67542462559621400261/62500000000000000000000) (592528336480003866574411/1000000000000000000000000) (5476753451389947/1000000000000000000000000) where
  r0 := (510822612873/1000000000000000000)
  k0 := (1689444094792097/500000000000000000)
  k6 := (5473023905514243/500000000000000000)
  q := (44228101926264029989/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15649]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15649]

theorem width_15650 : mW 15650 = 479512791138550 := by
  have hu : mW 15650 ≤ 479512791138550 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15650 ≤ 479512791138549 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15650 : RowArithmetic 15650 (540328867961155207247/500000000000000000000000) (148129802915400297061979/250000000000000000000000) (5475845675058221/1000000000000000000000000) where
  r0 := (510773653021/1000000000000000000)
  k0 := (3378726260740777/1000000000000000000)
  k6 := (10945698091454249/1000000000000000000)
  q := (44229515032385331367/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15650]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15650]

theorem width_15651 : mW 15651 = 479620038986625 := by
  have hu : mW 15651 ≤ 479620038986625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15651 ≤ 479620038986624 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15651 : RowArithmetic 15651 (270159018877621531259/250000000000000000000000) (592510087984378781255069/1000000000000000000000000) (547493810908347/100000000000000000000000) where
  r0 := (51072470099/100000000000000000)
  k0 := (1689282175002633/500000000000000000)
  k6 := (5472674202698927/500000000000000000)
  q := (176923712373440773899/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15651]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15651]

theorem width_15652 : mW 15652 = 479727303967218 := by
  have hu : mW 15652 ≤ 479727303967218 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15652 ≤ 479727303967217 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15652 : RowArithmetic 15652 (540307209858589773007/500000000000000000000000) (592500965448108517084293/1000000000000000000000000) (2737015376701551/500000000000000000000000) where
  r0 := (510675756777/1000000000000000000)
  k0 := (168920122868517/50000000000000000)
  k6 := (10944998752853947/1000000000000000000)
  q := (35385872887354354481/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15652]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15652]

theorem width_15653 : mW 15653 = 479834586081970 := by
  have hu : mW 15653 ≤ 479834586081970 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15653 ≤ 479834586081969 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15653 : RowArithmetic 15653 (1080592768541101454347/1000000000000000000000000) (296245922026281147960953/500000000000000000000000) (8551755637429/1562500000000000000000) where
  r0 := (255313410191/500000000000000000)
  k0 := (3378240582838603/1000000000000000000)
  k6 := (1368081141727147/125000000000000000)
  q := (88467508159775812689/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15653]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15653]

theorem width_15654 : mW 15654 = 479941885332524 := by
  have hu : mW 15654 ≤ 479941885332524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15654 ≤ 479941885332523 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15654 : RowArithmetic 15654 (216114224396192495237/200000000000000000000000) (592482723797512126180811/1000000000000000000000000) (5472216672675287/1000000000000000000000000) where
  r0 := (510577891801/1000000000000000000)
  k0 := (52782480099991/15625000000000000)
  k6 := (10944299548282189/1000000000000000000)
  q := (176940668021797634447/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15654]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15654]

theorem width_15655 : mW 15655 = 480049201720522 := by
  have hu : mW 15655 ≤ 480049201720522 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15655 ≤ 480049201720521 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15655 : RowArithmetic 15655 (270137370008868501047/250000000000000000000000) (296236802341365023233803/500000000000000000000000) (136782748687569/25000000000000000000000) where
  r0 := (255264485517/500000000000000000)
  k0 := (844479222013851/250000000000000000)
  k6 := (2735987499060909/250000000000000000)
  q := (88473159771763549239/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15655]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15655]

theorem width_15656 : mW 15656 = 480156535247606 := by
  have hu : mW 15656 ≤ 480156535247606 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15656 ≤ 480156535247605 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15656 : RowArithmetic 15656 (540263921351673945703/500000000000000000000000) (592464486707988155059153/1000000000000000000000000) (2735201716187241/500000000000000000000000) where
  r0 := (510480058079/1000000000000000000)
  k0 := (3377755067802527/1000000000000000000)
  k6 := (1367950059712021/125000000000000000)
  q := (176951970884757313573/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15656]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15656]

theorem width_15657 : mW 15657 = 480263885915419 := by
  have hu : mW 15657 ≤ 480263885915419 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15657 ≤ 480263885915418 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15657 : RowArithmetic 15657 (1080506209983296145839/1000000000000000000000000) (592455369873058628922633/1000000000000000000000000) (1093899425445593/200000000000000000000000) where
  r0 := (255215576467/500000000000000000)
  k0 := (422199158204597/125000000000000000)
  k6 := (5471625496317219/500000000000000000)
  q := (7078304881820222923/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15657]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15657]

theorem width_15658 : mW 15658 = 480371253725602 := by
  have hu : mW 15658 ≤ 480371253725602 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15658 ≤ 480371253725601 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15658 : RowArithmetic 15658 (216096916374806369227/200000000000000000000000) (296223127088856850152563/500000000000000000000000) (21361683718753/3906250000000000000000) where
  r0 := (510382255597/1000000000000000000)
  k0 := (1688715740777067/500000000000000000)
  k6 := (10942901541053099/1000000000000000000)
  q := (88481636512894583781/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15658]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15658]

theorem width_15659 : mW 15659 = 480478638679798 := by
  have hu : mW 15659 ≤ 480478638679798 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15659 ≤ 480478638679797 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15659 : RowArithmetic 15659 (1080462958374267920239/1000000000000000000000000) (148109284905431409726549/250000000000000000000000) (1366921286657613/250000000000000000000000) where
  r0 := (255166683033/500000000000000000)
  k0 := (3377269715550581/1000000000000000000)
  k6 := (2188510424589361/200000000000000000)
  q := (35393784765125076971/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15659]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15659]

theorem width_15660 : mW 15660 = 480586040779650 := by
  have hu : mW 15660 ≤ 480586040779650 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15660 ≤ 480586040779649 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15660 : RowArithmetic 15660 (1080441339482717756091/1000000000000000000000000) (59242802620486683150857/100000000000000000000000) (27333897355273/5000000000000000000000) where
  r0 := (25514224217/50000000000000000)
  k0 := (1688553983812703/500000000000000000)
  k6 := (5471101369155107/500000000000000000)
  q := (176974574445031510013/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15660]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15660]

theorem width_15661 : mW 15661 = 480693460026799 := by
  have hu : mW 15661 ≤ 480693460026799 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15661 ≤ 480693460026798 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15661 : RowArithmetic 15661 (1080419725198095810959/1000000000000000000000000) (148104728481727427060869/250000000000000000000000) (136646850130271/25000000000000000000000) where
  r0 := (510235610417/1000000000000000000)
  k0 := (3376946237774589/1000000000000000000)
  k6 := (547092669356899/50000000000000000)
  q := (35396044976804965067/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15661]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15661]

theorem width_15662 : mW 15662 = 480800896422888 := by
  have hu : mW 15662 ≤ 480800896422888 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15662 ≤ 480800896422887 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15662 : RowArithmetic 15662 (270099528879779097863/250000000000000000000000) (592409802787626727897701/1000000000000000000000000) (2732484374518401/500000000000000000000000) where
  r0 := (102037348859/200000000000000000)
  k0 := (844196131498527/250000000000000000)
  k6 := (2735376017356191/250000000000000000)
  q := (176985875142622610363/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15662]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15662]

theorem width_15663 : mW 15663 = 480908349969561 := by
  have hu : mW 15663 ≤ 480908349969561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15663 ≤ 480908349969560 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15663 : RowArithmetic 15663 (108037651044449395899/100000000000000000000000) (296200346393395216961437/500000000000000000000000) (5464063702470127/1000000000000000000000000) where
  r0 := (510137885973/1000000000000000000)
  k0 := (3376622832283249/1000000000000000000)
  k6 := (437646191406609/40000000000000000)
  q := (176991525220842141881/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15663]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15663]

theorem width_15664 : mW 15664 = 481015820668458 := by
  have hu : mW 15664 ≤ 481015820668458 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15664 ≤ 481015820668457 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15664 : RowArithmetic 15664 (540177454986472326163/500000000000000000000000) (592391583924173418979673/1000000000000000000000000) (218526354617941/40000000000000000000000) where
  r0 := (63761129431/125000000000000000)
  k0 := (84411528915867/25000000000000000)
  k6 := (5470402767177011/500000000000000000)
  q := (22124646889837586739/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15664]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15664]

theorem width_15665 : mW 15665 = 481123308521224 := by
  have hu : mW 15665 ≤ 481123308521224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15665 ≤ 481123308521223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15665 : RowArithmetic 15665 (135041664262897943273/125000000000000000000000) (592382476199548401543339/1000000000000000000000000) (2731127118954837/500000000000000000000000) where
  r0 := (6375502409/12500000000000000)
  k0 := (844074874762749/250000000000000000)
  k6 := (5470228158492909/500000000000000000)
  q := (2765669138065867777/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15665]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15665]

theorem width_15666 : mW 15666 = 481230813529501 := by
  have hu : mW 15666 ≤ 481230813529501 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15666 ≤ 481230813529500 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15666 : RowArithmetic 15666 (67519482677120442971/62500000000000000000000) (148093342403172023729001/250000000000000000000000) (2730674909895653/500000000000000000000000) where
  r0 := (254995678893/500000000000000000)
  k0 := (168806892976243/50000000000000000)
  k6 := (2735026783263819/250000000000000000)
  q := (88504237186701970919/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15666]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15666]

theorem width_15667 : mW 15667 = 481338335694931 := by
  have hu : mW 15667 ≤ 481338335694931 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15667 ≤ 481338335694930 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15667 : RowArithmetic 15667 (1080290136163892181411/1000000000000000000000000) (148091066040841306184213/250000000000000000000000) (5460445611031179/1000000000000000000000000) where
  r0 := (127485632661/250000000000000000)
  k0 := (3375976238052247/1000000000000000000)
  k6 := (10939757982557061/1000000000000000000)
  q := (177014123730283172001/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15667]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15667]

theorem width_15668 : mW 15668 = 481445875019157 := by
  have hu : mW 15668 ≤ 481445875019157 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15668 ≤ 481445875019156 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15668 : RowArithmetic 15668 (1080268554091795886703/1000000000000000000000000) (592355159851352739671201/1000000000000000000000000) (5459541611567061/1000000000000000000000000) where
  r0 := (509893711293/1000000000000000000)
  k0 := (84395365865811/25000000000000000)
  k6 := (2734852216371459/250000000000000000)
  q := (88509886453435245609/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15668]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15668]

theorem width_15669 : mW 15669 = 481553431503822 := by
  have hu : mW 15669 ≤ 481553431503822 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15669 ≤ 481553431503821 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15669 : RowArithmetic 15669 (108024697661635572039/100000000000000000000000) (592346056676423552223967/1000000000000000000000000) (1091727564267349/200000000000000000000000) where
  r0 := (509844899731/1000000000000000000)
  k0 := (337565304926141/100000000000000000)
  k6 := (10939059781836271/1000000000000000000)
  q := (35405084380636631947/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15669]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15669]

theorem width_15670 : mW 15670 = 481661005150570 := by
  have hu : mW 15670 ≤ 481661005150570 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15670 ≤ 481661005150569 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15670 : RowArithmetic 15670 (540112701868144676783/500000000000000000000000) (118467390927670114208761/200000000000000000000000) (2728867120139017/500000000000000000000000) where
  r0 := (127449023989/250000000000000000)
  k0 := (421936435241891/125000000000000000)
  k6 := (10938710731603031/1000000000000000000)
  q := (177031070719238435047/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15670]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15670]

theorem width_15671 : mW 15671 = 481768595961042 := by
  have hu : mW 15671 ≤ 481768595961042 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15671 ≤ 481768595961041 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15671 : RowArithmetic 15671 (135025479431289478297/125000000000000000000000) (592327853736906926295251/1000000000000000000000000) (5456830868328789/1000000000000000000000000) where
  r0 := (509747299967/1000000000000000000)
  k0 := (1687664966326437/500000000000000000)
  k6 := (5469180857390393/500000000000000000)
  q := (44259179838763392973/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15671]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15671]

theorem width_15672 : mW 15672 = 481876203936883 := by
  have hu : mW 15672 ≤ 481876203936883 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15672 ≤ 481876203936882 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15672 : RowArithmetic 15672 (135022783969644177673/125000000000000000000000) (118463750794373133256727/200000000000000000000000) (5455927705426849/1000000000000000000000000) where
  r0 := (254849255881/500000000000000000)
  k0 := (1687584200705309/500000000000000000)
  k6 := (5469006365682103/500000000000000000)
  q := (8852118390532291113/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15672]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15672]

theorem width_15673 : mW 15673 = 481983829079734 := by
  have hu : mW 15673 ≤ 481983829079734 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15673 ≤ 481983829079733 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15673 : RowArithmetic 15673 (67510044540970130811/62500000000000000000000) (592309655342999966549873/1000000000000000000000000) (5455024751510121/1000000000000000000000000) where
  r0 := (509649731339/1000000000000000000)
  k0 := (3375006888204327/1000000000000000000)
  k6 := (10937663781347963/1000000000000000000)
  q := (22131002010754054423/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15673]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15673]

theorem width_15674 : mW 15674 = 482091471391240 := by
  have hu : mW 15674 ≤ 482091471391240 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15674 ≤ 482091471391239 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15674 : RowArithmetic 15674 (540069579072070519219/500000000000000000000000) (74037569731260380002173/125000000000000000000000) (545412200651649/100000000000000000000000) where
  r0 := (63700119837/125000000000000000)
  k0 := (3374845393029969/1000000000000000000)
  k6 := (10937314864726729/1000000000000000000)
  q := (177053664181230657749/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15674]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15674]

theorem width_15675 : mW 15675 = 482199130873043 := by
  have hu : mW 15675 ≤ 482199130873043 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15675 ≤ 482199130873042 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15675 : RowArithmetic 15675 (1080117608221730822357/1000000000000000000000000) (592291461492888257769013/1000000000000000000000000) (5453219470383899/1000000000000000000000000) where
  r0 := (63694024229/125000000000000000)
  k0 := (168734195794341/50000000000000000)
  k6 := (5468482990747589/500000000000000000)
  q := (177059312096257733089/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15675]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15675]

theorem width_15676 : mW 15676 = 482306807526787 := by
  have hu : mW 15676 ≤ 482306807526787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15676 ≤ 482306807526786 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15676 : RowArithmetic 15676 (540048031443505929659/500000000000000000000000) (592282366271188875116247/1000000000000000000000000) (5452317143050289/1000000000000000000000000) where
  r0 := (101900687349/200000000000000000)
  k0 := (3374522456770847/1000000000000000000)
  k6 := (2187323426329597/200000000000000000)
  q := (177064959831130902387/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15676]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15676]

theorem width_15677 : mW 15677 = 482414501354114 := by
  have hu : mW 15677 ≤ 482414501354114 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15677 ≤ 482414501354113 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15677 : RowArithmetic 15677 (1080074522138705626689/1000000000000000000000000) (592273272184758387917373/1000000000000000000000000) (109028300489073/20000000000000000000000) where
  r0 := (63681835929/125000000000000000)
  k0 := (1687180507837351/500000000000000000)
  k6 := (5468134157589913/500000000000000000)
  q := (1416564859086939231/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15677]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15677]

theorem width_15678 : mW 15678 = 482522212356669 := by
  have hu : mW 15678 ≤ 482522212356669 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15678 ≤ 482522212356668 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15678 : RowArithmetic 15678 (270013246493883287251/250000000000000000000000) (2369056716933480817207/4000000000000000000000) (2725256557265979/500000000000000000000000) where
  r0 := (254702972947/500000000000000000)
  k0 := (1687099796302141/500000000000000000)
  k6 := (5467959766042689/500000000000000000)
  q := (177076254760484473039/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15678]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15678]

theorem width_15679 : mW 15679 = 482629940536095 := by
  have hu : mW 15679 ≤ 482629940536095 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15679 ≤ 482629940536094 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15679 : RowArithmetic 15679 (1080031454396216513163/1000000000000000000000000) (592255087416797930223963/1000000000000000000000000) (5449611413223237/1000000000000000000000000) where
  r0 := (254678606063/500000000000000000)
  k0 := (210877386721601/62500000000000000)
  k6 := (273389269558983/25000000000000000)
  q := (35416380390999868523/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15679]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15679]

theorem width_15680 : mW 15680 = 482737685894034 := by
  have hu : mW 15680 ≤ 482737685894034 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15680 ≤ 482737685894033 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15680 : RowArithmetic 15680 (216001985479895712893/200000000000000000000000) (592245996734815154503199/1000000000000000000000000) (1089741984093109/200000000000000000000000) where
  r0 := (509308486129/1000000000000000000)
  k0 := (16869384002523/5000000000000000)
  k6 := (10935222065996331/1000000000000000000)
  q := (5533985905294663831/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15680]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15680]

theorem width_15681 : mW 15681 = 482845448432131 := by
  have hu : mW 15681 ≤ 482845448432131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15681 ≤ 482845448432130 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15681 : RowArithmetic 15681 (134998550623005211969/125000000000000000000000) (592236907187195491520737/1000000000000000000000000) (5447808636196927/1000000000000000000000000) where
  r0 := (5092597679/10000000000000000)
  k0 := (1686857715736941/500000000000000000)
  k6 := (10934873382991093/1000000000000000000)
  q := (44273298950947850053/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15681]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15681]

theorem width_15682 : mW 15682 = 482953228152029 := by
  have hu : mW 15682 ≤ 482953228152029 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15682 ≤ 482953228152028 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15682 : RowArithmetic 15682 (107996688714862936093/100000000000000000000000) (592227818773712727010397/1000000000000000000000000) (5446907560355477/1000000000000000000000000) where
  r0 := (254605528719/500000000000000000)
  k0 := (26355891253537/7812500000000000)
  k6 := (10934524733338287/1000000000000000000)
  q := (177098842458103039969/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15682]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15682]

theorem width_15683 : mW 15683 = 483061025055371 := by
  have hu : mW 15683 ≤ 483061025055371 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15683 ≤ 483061025055370 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15683 : RowArithmetic 15683 (269986343472991367259/250000000000000000000000) (148054682873535158485753/250000000000000000000000) (544600669287931/100000000000000000000000) where
  r0 := (25458117737/50000000000000000)
  k0 := (1686696373716903/500000000000000000)
  k6 := (5467088058516299/500000000000000000)
  q := (44276122233095345903/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15683]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15683]

theorem width_15684 : mW 15684 = 483168839143802 := by
  have hu : mW 15684 ≤ 483168839143802 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15684 ≤ 483168839143801 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15684 : RowArithmetic 15684 (1079923865212773779669/1000000000000000000000000) (296104822674126512785837/500000000000000000000000) (5445106033706541/1000000000000000000000000) where
  r0 := (101822731961/200000000000000000)
  k0 := (843307858104091/250000000000000000)
  k6 := (2733456883517177/250000000000000000)
  q := (177110135226643650147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15684]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15684]

theorem width_15685 : mW 15685 = 483276670418965 := by
  have hu : mW 15685 ≤ 483276670418965 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15685 ≤ 483276670418964 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15685 : RowArithmetic 15685 (1079902361109779112183/1000000000000000000000000) (592200560335823870248619/1000000000000000000000000) (1361051395693833/250000000000000000000000) where
  r0 := (509064972631/1000000000000000000)
  k0 := (674614027079273/200000000000000000)
  k6 := (1366684873055163/125000000000000000)
  q := (177115781340907055831/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15685]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15685]

theorem width_15686 : mW 15686 = 483384518882503 := by
  have hu : mW 15686 ≤ 483384518882503 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15686 ≤ 483384518882502 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15686 : RowArithmetic 15686 (539940430790853370219/500000000000000000000000) (592191476456627100034043/1000000000000000000000000) (1360826335005967/250000000000000000000000) where
  r0 := (509016293217/1000000000000000000)
  k0 := (3372908856373079/1000000000000000000)
  k6 := (10933130468145073/1000000000000000000)
  q := (177121427275188814181/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15686]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15686]

theorem width_15687 : mW 15687 = 483492384536061 := by
  have hu : mW 15687 ≤ 483492384536061 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15687 ≤ 483492384536060 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15687 : RowArithmetic 15687 (1079859366627281788893/1000000000000000000000000) (118436478742087355101193/200000000000000000000000) (5442405305390333/1000000000000000000000000) where
  r0 := (508967621561/1000000000000000000)
  k0 := (3372747595342461/1000000000000000000)
  k6 := (5466390992587351/500000000000000000)
  q := (177127073029506135969/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15687]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15687]

theorem width_15688 : mW 15688 = 483600267381282 := by
  have hu : mW 15688 ≤ 483600267381282 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15688 ≤ 483600267381281 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15688 : RowArithmetic 15688 (1079837876245230440467/1000000000000000000000000) (118434662419405400401699/200000000000000000000000) (5441505478812957/1000000000000000000000000) where
  r0 := (508918957661/1000000000000000000)
  k0 := (674517270460093/200000000000000000)
  k6 := (10932433535524881/1000000000000000000)
  q := (88566359301938114611/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15688]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15688]

theorem width_15689 : mW 15689 = 483708167419811 := by
  have hu : mW 15689 ≤ 483708167419811 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15689 ≤ 483708167419810 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15689 : RowArithmetic 15689 (1079816390434278728703/1000000000000000000000000) (592164231616171957393041/1000000000000000000000000) (1360151465057493/250000000000000000000000) where
  r0 := (101774060303/200000000000000000)
  k0 := (3372425127243043/1000000000000000000)
  k6 := (10932085119190301/1000000000000000000)
  q := (17713836399831629923/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15689]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15689]

theorem width_15690 : mW 15690 = 483816084653290 := by
  have hu : mW 15690 ≤ 483816084653290 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15690 ≤ 483816084653289 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15690 : RowArithmetic 15690 (1079794909193154046249/1000000000000000000000000) (118431030453529154576763/200000000000000000000000) (1087941289915933/200000000000000000000000) where
  r0 := (254410826561/500000000000000000)
  k0 := (3372263920169461/1000000000000000000)
  k6 := (2732934184041413/250000000000000000)
  q := (22143001151605443567/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15690]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15690]

theorem width_15691 : mW 15691 = 483924019083365 := by
  have hu : mW 15691 ≤ 483924019083365 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15691 ≤ 483924019083364 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15691 : RowArithmetic 15691 (26994335813014575829/25000000000000000000000) (592146074051222824617373/1000000000000000000000000) (5438807246800301/1000000000000000000000000) where
  r0 := (99369729/195312500000000)
  k0 := (421512841384459/125000000000000000)
  k6 := (2732847096611407/250000000000000000)
  q := (35429930849495035389/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15691]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15691]

theorem width_15692 : mW 15692 = 484031970711679 := by
  have hu : mW 15692 ≤ 484031970711679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15692 ≤ 484031970711678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15692 : RowArithmetic 15692 (1079751960415293687951/1000000000000000000000000) (148034249241669361249307/250000000000000000000000) (5437908251830203/1000000000000000000000000) where
  r0 := (254362189793/500000000000000000)
  k0 := (337194155995431/100000000000000000)
  k6 := (5465520035012461/500000000000000000)
  q := (88577649551114190761/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15692]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15692]

theorem width_15693 : mW 15693 = 484139939539877 := by
  have hu : mW 15693 ≤ 484139939539877 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15693 ≤ 484139939539876 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15693 : RowArithmetic 15693 (1079730492876013859823/1000000000000000000000000) (592127921013783997742507/1000000000000000000000000) (2718504732303847/500000000000000000000000) where
  r0 := (508675754441/1000000000000000000)
  k0 := (3371780406811267/1000000000000000000)
  k6 := (1093069178689823/100000000000000000)
  q := (177160943777120356591/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15693]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15693]

theorem width_15694 : mW 15694 = 484247925569602 := by
  have hu : mW 15694 ≤ 484247925569602 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15694 ≤ 484247925569601 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15694 : RowArithmetic 15694 (269927257475368113459/250000000000000000000000) (74014855774039624101117/125000000000000000000000) (5436110885071141/1000000000000000000000000) where
  r0 := (6357839213/12500000000000000)
  k0 := (3371619271632549/1000000000000000000)
  k6 := (10930343537060247/1000000000000000000)
  q := (22145823534021036717/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15694]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15694]

theorem width_15695 : mW 15695 = 484355928802499 := by
  have hu : mW 15695 ≤ 484355928802499 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15695 ≤ 484355928802498 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15695 : RowArithmetic 15695 (1079687571490398225763/1000000000000000000000000) (148027443125512735509917/250000000000000000000000) (5435212513158913/1000000000000000000000000) where
  r0 := (63572315923/125000000000000000)
  k0 := (3371458154424047/1000000000000000000)
  k6 := (1366249415063209/125000000000000000)
  q := (35434446517477876361/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15695]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15695]

theorem width_15696 : mW 15696 = 484463949240212 := by
  have hu : mW 15696 ≤ 484463949240212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15696 ≤ 484463949240211 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15696 : RowArithmetic 15696 (1079666117641520685531/1000000000000000000000000) (592100699942760431303193/1000000000000000000000000) (1358578587202353/250000000000000000000000) where
  r0 := (50852992547/100000000000000000)
  k0 := (3371297055178393/1000000000000000000)
  k6 := (10929647137229203/1000000000000000000)
  q := (177177876722800806907/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15696]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15696]

theorem width_15697 : mW 15697 = 484571986884385 := by
  have hu : mW 15697 ≤ 484571986884385 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15697 ≤ 484571986884384 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15697 : RowArithmetic 15697 (539822334176784897859/500000000000000000000000) (296045814257110075731353/500000000000000000000000) (1086683278392213/200000000000000000000000) where
  r0 := (508481331297/1000000000000000000)
  k0 := (1685567986947423/500000000000000000)
  k6 := (546464949361277/50000000000000000)
  q := (44295880169604938103/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15697]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15697]

theorem width_15698 : mW 15698 = 484680041736663 := by
  have hu : mW 15698 ≤ 484680041736663 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15698 ≤ 484680041736662 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15698 : RowArithmetic 15698 (134952902953159458841/125000000000000000000000) (118416511643240964634199/200000000000000000000000) (1358129660638077/250000000000000000000000) where
  r0 := (254216372431/500000000000000000)
  k0 := (3370974910566037/1000000000000000000)
  k6 := (1366118858811173/125000000000000000)
  q := (177189164454263398957/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15698]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15698]

theorem width_15699 : mW 15699 = 484788113798690 := by
  have hu : mW 15699 ≤ 484788113798690 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15699 ≤ 484788113798689 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15699 : RowArithmetic 15699 (539800891727684589077/500000000000000000000000) (592073489048489163059101/1000000000000000000000000) (5431621100521613/1000000000000000000000000) where
  r0 := (101676833233/200000000000000000)
  k0 := (168540693259727/50000000000000000)
  k6 := (2732150696753859/250000000000000000)
  q := (88597404025174462219/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15699]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15699]

theorem width_15700 : mW 15700 = 484896203072111 := by
  have hu : mW 15700 ≤ 484896203072111 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15700 ≤ 484896203072110 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15700 : RowArithmetic 15700 (1079580347842581337221/1000000000000000000000000) (592064421010848045703227/1000000000000000000000000) (2715361882903731/500000000000000000000000) where
  r0 := (508335595203/1000000000000000000)
  k0 := (1685326418886491/500000000000000000)
  k6 := (10928254736798401/1000000000000000000)
  q := (8860022573334675201/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15700]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15700]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15626 then ⟨(33786842960063752789/31250000000000000000000), (592738522794691929857683/1000000000000000000000000), (687211313730833/125000000000000000000000)⟩ else
  if n = 15627 then ⟨(1081157203077768925191/1000000000000000000000000), (592729371666030720422963/1000000000000000000000000), (5496777877976743/1000000000000000000000000)⟩ else
  if n = 15628 then ⟨(1081135436083098614109/1000000000000000000000000), (592720221683814430034051/1000000000000000000000000), (2747932728954857/500000000000000000000000)⟩ else
  if n = 15629 then ⟨(540556836868364254149/500000000000000000000000), (118542214569562693793983/200000000000000000000000), (5494953249582447/1000000000000000000000000)⟩ else
  if n = 15630 then ⟨(1081091916037358734323/1000000000000000000000000), (592701925157798352935593/1000000000000000000000000), (2747020626465923/500000000000000000000000)⟩ else
  if n = 15631 then ⟨(1081070162983690192221/1000000000000000000000000), (592692778613539563284631/1000000000000000000000000), (109862589357897/20000000000000000000000)⟩ else
  if n = 15632 then ⟨(1081048414574423630489/1000000000000000000000000), (118536726642961537069067/200000000000000000000000), (1373054473602099/250000000000000000000000)⟩ else
  if n = 15633 then ⟨(540513335404130439431/500000000000000000000000), (4741395911690987574053/8000000000000000000000), (42900832284449/7812500000000000000000)⟩ else
  if n = 15634 then ⟨(1081004931683903615557/1000000000000000000000000), (592665345853007549527007/1000000000000000000000000), (5490395381835063/1000000000000000000000000)⟩ else
  if n = 15635 then ⟨(1080983197200054599143/1000000000000000000000000), (296328101944740362283239/500000000000000000000000), (2744742221311101/500000000000000000000000)⟩ else
  if n = 15636 then ⟨(1080961467355416436703/1000000000000000000000000), (74080882883820487068637/125000000000000000000000), (2744286857353961/500000000000000000000000)⟩ else
  if n = 15637 then ⟨(43237589685947700291/40000000000000000000000), (592637923396027911556531/1000000000000000000000000), (1371915799507323/250000000000000000000000)⟩ else
  if n = 15638 then ⟨(540459010789293326839/500000000000000000000000), (592628784865643832986639/1000000000000000000000000), (1371688223130851/250000000000000000000000)⟩ else
  if n = 15639 then ⟨(540448152821901591149/500000000000000000000000), (592619647479182620549733/1000000000000000000000000), (1371460699531843/250000000000000000000000)⟩ else
  if n = 15640 then ⟨(1080874594343046862871/1000000000000000000000000), (592610511236415446876987/1000000000000000000000000), (1096986582955667/200000000000000000000000)⟩ else
  if n = 15641 then ⟨(43234115507000892567/40000000000000000000000), (296300688068556716219229/500000000000000000000000), (5484023242413433/1000000000000000000000000)⟩ else
  if n = 15642 then ⟨(540415592819217769813/500000000000000000000000), (23703689687241911238877/40000000000000000000000), (2741556890484931/500000000000000000000000)⟩ else
  if n = 15643 then ⟨(270202372057998097813/250000000000000000000000), (148145777341997462935823/250000000000000000000000), (5482204530384821/1000000000000000000000000)⟩ else
  if n = 15644 then ⟨(1080787795454399184033/1000000000000000000000000), (118514795539542185345523/200000000000000000000000), (5481295490595529/1000000000000000000000000)⟩ else
  if n = 15645 then ⟨(1080766107304363308869/1000000000000000000000000), (148141211792495624093897/250000000000000000000000), (1096077332307851/200000000000000000000000)⟩ else
  if n = 15646 then ⟨(540372211890295696181/500000000000000000000000), (59255571778457597685299/100000000000000000000000), (5479478043153243/1000000000000000000000000)⟩ else
  if n = 15647 then ⟨(1080722744881791749789/1000000000000000000000000), (592546589541262978021729/1000000000000000000000000), (684821204421851/125000000000000000000000)⟩ else
  if n = 15648 then ⟨(135087633825834068139/125000000000000000000000), (592537462439815025126797/1000000000000000000000000), (5477661438141263/1000000000000000000000000)⟩ else
  if n = 15649 then ⟨(67542462559621400261/62500000000000000000000), (592528336480003866574411/1000000000000000000000000), (5476753451389947/1000000000000000000000000)⟩ else
  if n = 15650 then ⟨(540328867961155207247/500000000000000000000000), (148129802915400297061979/250000000000000000000000), (5475845675058221/1000000000000000000000000)⟩ else
  if n = 15651 then ⟨(270159018877621531259/250000000000000000000000), (592510087984378781255069/1000000000000000000000000), (547493810908347/100000000000000000000000)⟩ else
  if n = 15652 then ⟨(540307209858589773007/500000000000000000000000), (592500965448108517084293/1000000000000000000000000), (2737015376701551/500000000000000000000000)⟩ else
  if n = 15653 then ⟨(1080592768541101454347/1000000000000000000000000), (296245922026281147960953/500000000000000000000000), (8551755637429/1562500000000000000000)⟩ else
  if n = 15654 then ⟨(216114224396192495237/200000000000000000000000), (592482723797512126180811/1000000000000000000000000), (5472216672675287/1000000000000000000000000)⟩ else
  if n = 15655 then ⟨(270137370008868501047/250000000000000000000000), (296236802341365023233803/500000000000000000000000), (136782748687569/25000000000000000000000)⟩ else
  if n = 15656 then ⟨(540263921351673945703/500000000000000000000000), (592464486707988155059153/1000000000000000000000000), (2735201716187241/500000000000000000000000)⟩ else
  if n = 15657 then ⟨(1080506209983296145839/1000000000000000000000000), (592455369873058628922633/1000000000000000000000000), (1093899425445593/200000000000000000000000)⟩ else
  if n = 15658 then ⟨(216096916374806369227/200000000000000000000000), (296223127088856850152563/500000000000000000000000), (21361683718753/3906250000000000000000)⟩ else
  if n = 15659 then ⟨(1080462958374267920239/1000000000000000000000000), (148109284905431409726549/250000000000000000000000), (1366921286657613/250000000000000000000000)⟩ else
  if n = 15660 then ⟨(1080441339482717756091/1000000000000000000000000), (59242802620486683150857/100000000000000000000000), (27333897355273/5000000000000000000000)⟩ else
  if n = 15661 then ⟨(1080419725198095810959/1000000000000000000000000), (148104728481727427060869/250000000000000000000000), (136646850130271/25000000000000000000000)⟩ else
  if n = 15662 then ⟨(270099528879779097863/250000000000000000000000), (592409802787626727897701/1000000000000000000000000), (2732484374518401/500000000000000000000000)⟩ else
  if n = 15663 then ⟨(108037651044449395899/100000000000000000000000), (296200346393395216961437/500000000000000000000000), (5464063702470127/1000000000000000000000000)⟩ else
  if n = 15664 then ⟨(540177454986472326163/500000000000000000000000), (592391583924173418979673/1000000000000000000000000), (218526354617941/40000000000000000000000)⟩ else
  if n = 15665 then ⟨(135041664262897943273/125000000000000000000000), (592382476199548401543339/1000000000000000000000000), (2731127118954837/500000000000000000000000)⟩ else
  if n = 15666 then ⟨(67519482677120442971/62500000000000000000000), (148093342403172023729001/250000000000000000000000), (2730674909895653/500000000000000000000000)⟩ else
  if n = 15667 then ⟨(1080290136163892181411/1000000000000000000000000), (148091066040841306184213/250000000000000000000000), (5460445611031179/1000000000000000000000000)⟩ else
  if n = 15668 then ⟨(1080268554091795886703/1000000000000000000000000), (592355159851352739671201/1000000000000000000000000), (5459541611567061/1000000000000000000000000)⟩ else
  if n = 15669 then ⟨(108024697661635572039/100000000000000000000000), (592346056676423552223967/1000000000000000000000000), (1091727564267349/200000000000000000000000)⟩ else
  if n = 15670 then ⟨(540112701868144676783/500000000000000000000000), (118467390927670114208761/200000000000000000000000), (2728867120139017/500000000000000000000000)⟩ else
  if n = 15671 then ⟨(135025479431289478297/125000000000000000000000), (592327853736906926295251/1000000000000000000000000), (5456830868328789/1000000000000000000000000)⟩ else
  if n = 15672 then ⟨(135022783969644177673/125000000000000000000000), (118463750794373133256727/200000000000000000000000), (5455927705426849/1000000000000000000000000)⟩ else
  if n = 15673 then ⟨(67510044540970130811/62500000000000000000000), (592309655342999966549873/1000000000000000000000000), (5455024751510121/1000000000000000000000000)⟩ else
  if n = 15674 then ⟨(540069579072070519219/500000000000000000000000), (74037569731260380002173/125000000000000000000000), (545412200651649/100000000000000000000000)⟩ else
  if n = 15675 then ⟨(1080117608221730822357/1000000000000000000000000), (592291461492888257769013/1000000000000000000000000), (5453219470383899/1000000000000000000000000)⟩ else
  if n = 15676 then ⟨(540048031443505929659/500000000000000000000000), (592282366271188875116247/1000000000000000000000000), (5452317143050289/1000000000000000000000000)⟩ else
  if n = 15677 then ⟨(1080074522138705626689/1000000000000000000000000), (592273272184758387917373/1000000000000000000000000), (109028300489073/20000000000000000000000)⟩ else
  if n = 15678 then ⟨(270013246493883287251/250000000000000000000000), (2369056716933480817207/4000000000000000000000), (2725256557265979/500000000000000000000000)⟩ else
  if n = 15679 then ⟨(1080031454396216513163/1000000000000000000000000), (592255087416797930223963/1000000000000000000000000), (5449611413223237/1000000000000000000000000)⟩ else
  if n = 15680 then ⟨(216001985479895712893/200000000000000000000000), (592245996734815154503199/1000000000000000000000000), (1089741984093109/200000000000000000000000)⟩ else
  if n = 15681 then ⟨(134998550623005211969/125000000000000000000000), (592236907187195491520737/1000000000000000000000000), (5447808636196927/1000000000000000000000000)⟩ else
  if n = 15682 then ⟨(107996688714862936093/100000000000000000000000), (592227818773712727010397/1000000000000000000000000), (5446907560355477/1000000000000000000000000)⟩ else
  if n = 15683 then ⟨(269986343472991367259/250000000000000000000000), (148054682873535158485753/250000000000000000000000), (544600669287931/100000000000000000000000)⟩ else
  if n = 15684 then ⟨(1079923865212773779669/1000000000000000000000000), (296104822674126512785837/500000000000000000000000), (5445106033706541/1000000000000000000000000)⟩ else
  if n = 15685 then ⟨(1079902361109779112183/1000000000000000000000000), (592200560335823870248619/1000000000000000000000000), (1361051395693833/250000000000000000000000)⟩ else
  if n = 15686 then ⟨(539940430790853370219/500000000000000000000000), (592191476456627100034043/1000000000000000000000000), (1360826335005967/250000000000000000000000)⟩ else
  if n = 15687 then ⟨(1079859366627281788893/1000000000000000000000000), (118436478742087355101193/200000000000000000000000), (5442405305390333/1000000000000000000000000)⟩ else
  if n = 15688 then ⟨(1079837876245230440467/1000000000000000000000000), (118434662419405400401699/200000000000000000000000), (5441505478812957/1000000000000000000000000)⟩ else
  if n = 15689 then ⟨(1079816390434278728703/1000000000000000000000000), (592164231616171957393041/1000000000000000000000000), (1360151465057493/250000000000000000000000)⟩ else
  if n = 15690 then ⟨(1079794909193154046249/1000000000000000000000000), (118431030453529154576763/200000000000000000000000), (1087941289915933/200000000000000000000000)⟩ else
  if n = 15691 then ⟨(26994335813014575829/25000000000000000000000), (592146074051222824617373/1000000000000000000000000), (5438807246800301/1000000000000000000000000)⟩ else
  if n = 15692 then ⟨(1079751960415293687951/1000000000000000000000000), (148034249241669361249307/250000000000000000000000), (5437908251830203/1000000000000000000000000)⟩ else
  if n = 15693 then ⟨(1079730492876013859823/1000000000000000000000000), (592127921013783997742507/1000000000000000000000000), (2718504732303847/500000000000000000000000)⟩ else
  if n = 15694 then ⟨(269927257475368113459/250000000000000000000000), (74014855774039624101117/125000000000000000000000), (5436110885071141/1000000000000000000000000)⟩ else
  if n = 15695 then ⟨(1079687571490398225763/1000000000000000000000000), (148027443125512735509917/250000000000000000000000), (5435212513158913/1000000000000000000000000)⟩ else
  if n = 15696 then ⟨(1079666117641520685531/1000000000000000000000000), (592100699942760431303193/1000000000000000000000000), (1358578587202353/250000000000000000000000)⟩ else
  if n = 15697 then ⟨(539822334176784897859/500000000000000000000000), (296045814257110075731353/500000000000000000000000), (1086683278392213/200000000000000000000000)⟩ else
  if n = 15698 then ⟨(134952902953159458841/125000000000000000000000), (118416511643240964634199/200000000000000000000000), (1358129660638077/250000000000000000000000)⟩ else
  if n = 15699 then ⟨(539800891727684589077/500000000000000000000000), (592073489048489163059101/1000000000000000000000000), (5431621100521613/1000000000000000000000000)⟩ else
  ⟨(1079580347842581337221/1000000000000000000000000), (592064421010848045703227/1000000000000000000000000), (2715361882903731/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15626 ≤ n) (hb : n ≤ 15700) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15626
  · exact row_15627
  · exact row_15628
  · exact row_15629
  · exact row_15630
  · exact row_15631
  · exact row_15632
  · exact row_15633
  · exact row_15634
  · exact row_15635
  · exact row_15636
  · exact row_15637
  · exact row_15638
  · exact row_15639
  · exact row_15640
  · exact row_15641
  · exact row_15642
  · exact row_15643
  · exact row_15644
  · exact row_15645
  · exact row_15646
  · exact row_15647
  · exact row_15648
  · exact row_15649
  · exact row_15650
  · exact row_15651
  · exact row_15652
  · exact row_15653
  · exact row_15654
  · exact row_15655
  · exact row_15656
  · exact row_15657
  · exact row_15658
  · exact row_15659
  · exact row_15660
  · exact row_15661
  · exact row_15662
  · exact row_15663
  · exact row_15664
  · exact row_15665
  · exact row_15666
  · exact row_15667
  · exact row_15668
  · exact row_15669
  · exact row_15670
  · exact row_15671
  · exact row_15672
  · exact row_15673
  · exact row_15674
  · exact row_15675
  · exact row_15676
  · exact row_15677
  · exact row_15678
  · exact row_15679
  · exact row_15680
  · exact row_15681
  · exact row_15682
  · exact row_15683
  · exact row_15684
  · exact row_15685
  · exact row_15686
  · exact row_15687
  · exact row_15688
  · exact row_15689
  · exact row_15690
  · exact row_15691
  · exact row_15692
  · exact row_15693
  · exact row_15694
  · exact row_15695
  · exact row_15696
  · exact row_15697
  · exact row_15698
  · exact row_15699
  · exact row_15700

end BstLean.Part271.R3.Rows15626
