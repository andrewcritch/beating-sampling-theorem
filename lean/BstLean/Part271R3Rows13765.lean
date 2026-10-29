import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13765–13839. -/
namespace BstLean.Part271.R3.Rows13765
open Real BstLean.Part130 BstLean.Part227

theorem width_13765 : mW 13765 = 305996708570792 := by
  have hu : mW 13765 ≤ 305996708570792 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13765 ≤ 305996708570791 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13765 : RowArithmetic 13765 (282854155991376430937/250000000000000000000000) (612038535468862408396663/1000000000000000000000000) (1528933228341377/200000000000000000000000) where
  r0 := (154801685519/250000000000000000)
  k0 := (3720117025766609/1000000000000000000)
  k6 := (11671119832313037/1000000000000000000)
  q := (165921668265480021361/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13765]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13765]

theorem width_13766 : mW 13766 = 306074520829421 := by
  have hu : mW 13766 ≤ 306074520829421 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13766 ≤ 306074520829420 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13766 : RowArithmetic 13766 (70711459429150089531/62500000000000000000000) (306013385974968398673389/500000000000000000000000) (7643219236998773/1000000000000000000000000) where
  r0 := (619139271987/1000000000000000000)
  k0 := (1859957172148693/500000000000000000)
  k6 := (11670695913535049/1000000000000000000)
  q := (165927695096388294283/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13766]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13766]

theorem width_13767 : mW 13767 = 306152347220572 := by
  have hu : mW 13767 ≤ 306152347220572 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13767 ≤ 306152347220571 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13767 : RowArithmetic 13767 (282837521467223482249/250000000000000000000000) (612015010143586812893/1000000000000000000000) (7641772715025159/1000000000000000000000000) where
  r0 := (12381436283/20000000000000000)
  k0 := (929927922148153/250000000000000000)
  k6 := (145878400511831/12500000000000000)
  q := (33186744341679555597/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13767]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13767]

theorem width_13768 : mW 13768 = 306230187745787 := by
  have hu : mW 13768 ≤ 306230187745787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13768 ≤ 306230187745786 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13768 : RowArithmetic 13768 (1131316828970400003971/1000000000000000000000000) (612003250049414242683421/1000000000000000000000000) (7640326575656033/1000000000000000000000000) where
  r0 := (309502184281/500000000000000000)
  k0 := (743901811729497/200000000000000000)
  k6 := (11669848214538941/1000000000000000000)
  q := (41484937025383080603/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13768]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13768]

theorem width_13769 : mW 13769 = 306308042406604 := by
  have hu : mW 13769 ≤ 306308042406604 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13769 ≤ 306308042406603 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13769 : RowArithmetic 13769 (1131283580168340082799/1000000000000000000000000) (152997872916755235790671/250000000000000000000000) (3819440409380771/500000000000000000000000) where
  r0 := (618936935219/1000000000000000000)
  k0 := (1859653227227099/500000000000000000)
  k6 := (11669424434304047/1000000000000000000)
  q := (82972887137907886591/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13769]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13769]

theorem width_13770 : mW 13770 = 306385911204565 := by
  have hu : mW 13770 ≤ 306385911204565 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13770 ≤ 306385911204564 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13770 : RowArithmetic 13770 (141406292432516632717/125000000000000000000000) (152994933749002224784673/250000000000000000000000) (1527487088842357/200000000000000000000000) where
  r0 := (618869514119/1000000000000000000)
  k0 := (929775969002737/250000000000000000)
  k6 := (1458625087529177/125000000000000000)
  q := (165951800231271971581/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13770]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13770]

theorem width_13771 : mW 13771 = 306463794141208 := by
  have hu : mW 13771 ≤ 306463794141208 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13771 ≤ 306463794141207 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13771 : RowArithmetic 13771 (226243421368640293681/200000000000000000000000) (611967980035980254270877/1000000000000000000000000) (381799522593851/50000000000000000000000) where
  r0 := (618802105259/1000000000000000000)
  k0 := (3718901323312929/1000000000000000000)
  k6 := (5834288506159333/500000000000000000)
  q := (165957825967924754567/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13771]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13771]

theorem width_13772 : mW 13772 = 306541691218076 := by
  have hu : mW 13772 ≤ 306541691218076 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13772 ≤ 306541691218075 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13772 : RowArithmetic 13772 (565591941157482829101/500000000000000000000000) (305978113393268650270439/500000000000000000000000) (7634545841627433/1000000000000000000000000) where
  r0 := (123746941727/200000000000000000)
  k0 := (464837349544041/125000000000000000)
  k6 := (11668153370551419/1000000000000000000)
  q := (165963851485797954773/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13772]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13772]

theorem width_13773 : mW 13773 = 306619602436706 := by
  have hu : mW 13773 ≤ 306619602436706 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13773 ≤ 306619602436705 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13773 : RowArithmetic 13773 (1131150665872850903501/1000000000000000000000000) (611944475247282405378939/1000000000000000000000000) (1526620322666683/200000000000000000000000) where
  r0 := (154666831061/250000000000000000)
  k0 := (743699259024867/200000000000000000)
  k6 := (5833864887461649/500000000000000000)
  q := (165969876784915400503/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13773]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13773]

theorem width_13774 : mW 13774 = 306697527798641 := by
  have hu : mW 13774 ≤ 306697527798641 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13774 ≤ 306697527798640 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13774 : RowArithmetic 13774 (1131117457514279661349/1000000000000000000000000) (611932725417818104947043/1000000000000000000000000) (3815828883432631/500000000000000000000000) where
  r0 := (618599952083/1000000000000000000)
  k0 := (3718293819624137/1000000000000000000)
  k6 := (1166730622542593/100000000000000000)
  q := (82987950932650457869/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13774]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13774]

theorem width_13775 : mW 13775 = 306775467305420 := by
  have hu : mW 13775 ≤ 306775467305420 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13775 ≤ 306775467305419 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13775 : RowArithmetic 13775 (565542128618339007339/500000000000000000000000) (24476839091909881239481/40000000000000000000000) (7630214302093427/1000000000000000000000000) where
  r0 := (618532592149/1000000000000000000)
  k0 := (3718091369846921/1000000000000000000)
  k6 := (583344136102547/50000000000000000)
  q := (41495481681744580033/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13775]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13775]

theorem width_13776 : mW 13776 = 306853420958584 := by
  have hu : mW 13776 ≤ 306853420958584 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13776 ≤ 306853420958583 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13776 : RowArithmetic 13776 (1131051065037471807781/1000000000000000000000000) (305954615443335958940551/500000000000000000000000) (3814385609444183/500000000000000000000000) where
  r0 := (618465244439/1000000000000000000)
  k0 := (116184029555871/31250000000000000)
  k6 := (291661481619749/25000000000000000)
  q := (8299397568498571451/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13776]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13776]

theorem width_13777 : mW 13777 = 306931388759673 := by
  have hu : mW 13777 ≤ 306931388759673 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13777 ≤ 306931388759672 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13777 : RowArithmetic 13777 (1131017880914088576933/1000000000000000000000000) (611897486184195690615551/1000000000000000000000000) (953416064640077/125000000000000000000000) where
  r0 := (12367958179/20000000000000000)
  k0 := (3717686547442173/1000000000000000000)
  k6 := (11666035853634621/1000000000000000000)
  q := (165993975794304053413/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13777]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13777]

theorem width_13778 : mW 13778 = 307009370710227 := by
  have hu : mW 13778 ≤ 307009370710227 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13778 ≤ 307009370710226 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13778 : RowArithmetic 13778 (141373088107994613241/125000000000000000000000) (611885743189921383863333/1000000000000000000000000) (7625886196660769/1000000000000000000000000) where
  r0 := (618330585679/1000000000000000000)
  k0 := (1858742087402503/500000000000000000)
  k6 := (11665612488576557/1000000000000000000)
  q := 166
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13778]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13778]

theorem width_13779 : mW 13779 = 307087366811788 := by
  have hu : mW 13779 ≤ 307087366811788 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13779 ≤ 307087366811787 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13779 : RowArithmetic 13779 (565475768442252570499/500000000000000000000000) (305937000951726052611019/500000000000000000000000) (7624444257379421/1000000000000000000000000) where
  r0 := (309131637311/500000000000000000)
  k0 := (29041264280223/7812500000000000)
  k6 := (2333037833921481/200000000000000000)
  q := (83003011993541535577/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13779]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13779]

theorem width_13780 : mW 13780 = 307165377065896 := by
  have hu : mW 13780 ≤ 307165377065896 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13780 ≤ 307165377065895 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13780 : RowArithmetic 13780 (1130918376973163960963/1000000000000000000000000) (38241391395274450008551/62500000000000000000000) (304920107965891/40000000000000000000000) where
  r0 := (618195975777/1000000000000000000)
  k0 := (929269876657743/250000000000000000)
  k6 := (5832382948359401/500000000000000000)
  q := (83006023877788532463/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13780]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13780]

theorem width_13781 : mW 13781 = 307243401474091 := by
  have hu : mW 13781 ≤ 307243401474091 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13781 ≤ 307243401474090 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13781 : RowArithmetic 13781 (1130885225127365090517/1000000000000000000000000) (152962631113085497639261/250000000000000000000000) (7621561521835087/1000000000000000000000000) where
  r0 := (30906434457/50000000000000000)
  k0 := (3716877211084461/1000000000000000000)
  k6 := (1166434266990239/100000000000000000)
  q := (41504517826376443763/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13781]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13781]

theorem width_13782 : mW 13782 = 307321440037915 := by
  have hu : mW 13782 ≤ 307321440037915 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13782 ≤ 307321440037914 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13782 : RowArithmetic 13782 (226170416268908003353/200000000000000000000000) (76479848535863511627813/125000000000000000000000) (7620120725313619/1000000000000000000000000) where
  r0 := (618061414709/1000000000000000000)
  k0 := (464584367653399/125000000000000000)
  k6 := (1166391948914981/100000000000000000)
  q := (166024094636892990949/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13782]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13782]

theorem width_13783 : mW 13783 = 307399492758908 := by
  have hu : mW 13783 ≤ 307399492758908 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13783 ≤ 307399492758907 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13783 : RowArithmetic 13783 (565409472811061278061/500000000000000000000000) (611827053827693025925557/1000000000000000000000000) (952335038681717/125000000000000000000000) where
  r0 := (617994152479/1000000000000000000)
  k0 := (148658907881933/40000000000000000)
  k6 := (11663496354452707/1000000000000000000)
  q := (83015058874881248861/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13783]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13783]

theorem width_13784 : mW 13784 = 307477559638611 := by
  have hu : mW 13784 ≤ 307477559638611 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13784 ≤ 307477559638610 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13784 : RowArithmetic 13784 (565392908978773464157/500000000000000000000000) (24472612842972028610639/40000000000000000000000) (7617240274126337/1000000000000000000000000) where
  r0 := (617926902449/1000000000000000000)
  k0 := (1858135239274523/500000000000000000)
  k6 := (1457884158225341/125000000000000000)
  q := (16214466859779109/97656250000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13784]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13784]

theorem width_13785 : mW 13785 = 307555640678565 := by
  have hu : mW 13785 ≤ 307555640678565 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13785 ≤ 307555640678564 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13785 : RowArithmetic 13785 (1130752698348248397823/1000000000000000000000000) (611803590026334985371483/1000000000000000000000000) (7615800619202371/1000000000000000000000000) where
  r0 := (123571932923/200000000000000000)
  k0 := (3716068285721517/1000000000000000000)
  k6 := (5831325111595761/500000000000000000)
  q := (166042163320043502739/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13785]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13785]

theorem width_13786 : mW 13786 = 307633735880311 := by
  have hu : mW 13786 ≤ 307633735880311 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13786 ≤ 307633735880310 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13786 : RowArithmetic 13786 (1130719586791663273341/1000000000000000000000000) (152947965170849969471641/250000000000000000000000) (1522872268910569/200000000000000000000000) where
  r0 := (308896219487/500000000000000000)
  k0 := (3715866118560907/1000000000000000000)
  k6 := (583111361330537/50000000000000000)
  q := (166048185777502549623/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13786]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13786]

theorem width_13787 : mW 13787 = 307711845245390 := by
  have hu : mW 13787 ≤ 307711845245390 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13787 ≤ 307711845245389 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13787 : RowArithmetic 13787 (1130686483285228907219/1000000000000000000000000) (611780133045099567380271/1000000000000000000000000) (380646122502441/50000000000000000000000) where
  r0 := (617725225523/1000000000000000000)
  k0 := (232228998566399/62500000000000000)
  k6 := (2915451069013009/250000000000000000)
  q := (166054208016538984667/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13787]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13787]

theorem width_13788 : mW 13788 = 307789968775342 := by
  have hu : mW 13788 ≤ 307789968775342 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13788 ≤ 307789968775341 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13788 : RowArithmetic 13788 (4522613551305537339/4000000000000000000000) (611768407111038295041747/1000000000000000000000000) (1522296787112287/200000000000000000000000) where
  r0 := (308829012129/500000000000000000)
  k0 := (743092372243621/200000000000000000)
  k6 := (11661381371507063/1000000000000000000)
  q := (166060230037176571413/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13788]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13788]

theorem width_13789 : mW 13789 = 307868106471710 := by
  have hu : mW 13789 ≤ 307868106471710 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13789 ≤ 307868106471709 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13789 : RowArithmetic 13789 (282655075103141928507/250000000000000000000000) (611756682880820541377753/1000000000000000000000000) (1902511450240453/250000000000000000000000) where
  r0 := (617590835177/1000000000000000000)
  k0 := (3715259771026241/1000000000000000000)
  k6 := (291523962824187/25000000000000000)
  q := (20758281479929883637/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13789]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13789]

theorem width_13790 : mW 13790 = 307946258336035 := by
  have hu : mW 13790 ≤ 307946258336035 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13790 ≤ 307946258336034 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13790 : RowArithmetic 13790 (226117444208243905181/200000000000000000000000) (611744960354050813537517/1000000000000000000000000) (304344321844847/40000000000000000000000) where
  r0 := (154380914569/250000000000000000)
  k0 := (1857528853239473/500000000000000000)
  k6 := (11660535700424947/1000000000000000000)
  q := (33214454684670046529/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13790]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13790]

theorem width_13791 : mW 13791 = 308024424369857 := by
  have hu : mW 13791 ≤ 308024424369857 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13791 ≤ 308024424369856 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13791 : RowArithmetic 13791 (565277074854890965859/500000000000000000000000) (152933309882583426081113/250000000000000000000000) (760717067091083/100000000000000000000000) where
  r0 := (617456493553/1000000000000000000)
  k0 := (928713916893597/250000000000000000)
  k6 := (2915028233467781/250000000000000000)
  q := (4151957369723345317/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13791]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13791]

theorem width_13792 : mW 13792 = 308102604574717 := by
  have hu : mW 13792 ≤ 308102604574717 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13792 ≤ 308102604574716 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13792 : RowArithmetic 13792 (565260543207848746947/500000000000000000000000) (24468860816370963734693/40000000000000000000000) (7605733675202109/1000000000000000000000000) where
  r0 := (154347335251/250000000000000000)
  k0 := (3714653654304719/1000000000000000000)
  k6 := (11659690213297677/1000000000000000000)
  q := (166084315936213555517/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13792]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13792]

theorem width_13793 : mW 13793 = 308180798952159 := by
  have hu : mW 13793 ≤ 308180798952159 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13793 ≤ 308180798952158 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13793 : RowArithmetic 13793 (1130488031156407899799/1000000000000000000000000) (305854901495238433846771/500000000000000000000000) (7604297058866327/1000000000000000000000000) where
  r0 := (617322200627/1000000000000000000)
  k0 := (464306458333513/125000000000000000)
  k6 := (11659267538696269/1000000000000000000)
  q := (5190323027037912599/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13793]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13793]

theorem width_13794 : mW 13794 = 308259007503721 := by
  have hu : mW 13794 ≤ 308259007503721 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13794 ≤ 308259007503720 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13794 : RowArithmetic 13794 (1130454983929359709117/1000000000000000000000000) (611698087273547046137649/1000000000000000000000000) (7602860821775003/1000000000000000000000000) where
  r0 := (308627536209/500000000000000000)
  k0 := (3714249704656689/1000000000000000000)
  k6 := (1165884491005857/100000000000000000)
  q := (8304817878797824667/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13794]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13794]

theorem width_13795 : mW 13795 = 308337230230948 := by
  have hu : mW 13795 ≤ 308337230230948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13795 ≤ 308337230230947 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13795 : RowArithmetic 13795 (1130421944731996051997/1000000000000000000000000) (611686373258089828031273/1000000000000000000000000) (1520284992759907/200000000000000000000000) where
  r0 := (308593978187/500000000000000000)
  k0 := (371404776826563/100000000000000000)
  k6 := (11658422327376249/1000000000000000000)
  q := (166102378068467159439/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13795]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13795]

theorem width_13796 : mW 13796 = 308415467135378 := by
  have hu : mW 13796 ≤ 308415467135378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13796 ≤ 308415467135377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13796 : RowArithmetic 13796 (1130388913561765565329/1000000000000000000000000) (152918665235927611238577/250000000000000000000000) (151999789696231/20000000000000000000000) where
  r0 := (154280213123/250000000000000000)
  k0 := (3713845857490077/1000000000000000000)
  k6 := (11657999790640979/1000000000000000000)
  q := (166108398342768930571/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13796]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13796]

theorem width_13797 : mW 13797 = 308493718218555 := by
  have hu : mW 13797 ≤ 308493718218555 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13797 ≤ 308493718218554 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13797 : RowArithmetic 13797 (1130355890416114096553/1000000000000000000000000) (611662950330014367171553/1000000000000000000000000) (7598554384682581/1000000000000000000000000) where
  r0 := (2410366253/3906250000000000)
  k0 := (928410993080543/250000000000000000)
  k6 := (5828788649922217/500000000000000000)
  q := (166114418398885531541/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13797]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13797]

theorem width_13798 : mW 13798 = 308571983482020 := by
  have hu : mW 13798 ≤ 308571983482020 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13798 ≤ 308571983482019 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13798 : RowArithmetic 13798 (565161437646245222689/500000000000000000000000) (611651241416607095536163/1000000000000000000000000) (7597119663284289/1000000000000000000000000) where
  r0 := (616986681201/1000000000000000000)
  k0 := (928360528190771/250000000000000000)
  k6 := (1165715485497829/100000000000000000)
  q := (33224087647368136571/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13798]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13798]

theorem width_13799 : mW 13799 = 308650262927315 := by
  have hu : mW 13799 ≤ 308650262927315 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13799 ≤ 308650262927314 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13799 : RowArithmetic 13799 (282572467047085952937/250000000000000000000000) (611639534203094343448113/1000000000000000000000000) (1519137064097673/200000000000000000000000) where
  r0 := (308459806893/500000000000000000)
  k0 := (3713240278801939/1000000000000000000)
  k6 := (5828366228017113/500000000000000000)
  q := (166126457856658100721/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13799]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13799]

theorem width_13800 : mW 13800 = 308728556555981 := by
  have hu : mW 13800 ≤ 308728556555981 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13800 ≤ 308728556555980 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13800 : RowArithmetic 13800 (1130256869101125069831/1000000000000000000000000) (152906957172270468211811/250000000000000000000000) (379712567808329/50000000000000000000000) where
  r0 := (616852558521/1000000000000000000)
  k0 := (742607694087379/200000000000000000)
  k6 := (11656310103003923/1000000000000000000)
  q := (41533119314590374263/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13800]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13800]

theorem width_13801 : mW 13801 = 308806864369560 := by
  have hu : mW 13801 ≤ 308806864369560 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13801 ≤ 308806864369559 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13801 : RowArithmetic 13801 (1130223878028285493481/1000000000000000000000000) (611616124874175575680581/1000000000000000000000000) (7592817770190733/1000000000000000000000000) where
  r0 := (616785515403/1000000000000000000)
  k0 := (1856418343831547/500000000000000000)
  k6 := (5827943897939531/500000000000000000)
  q := (20767312055246822433/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13801]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13801]

theorem width_13802 : mW 13802 = 308885186369594 := by
  have hu : mW 13802 ≤ 308885186369594 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13802 ≤ 308885186369593 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13802 : RowArithmetic 13802 (1130190894967277393089/1000000000000000000000000) (305802211378990770525657/500000000000000000000000) (7591384562432679/1000000000000000000000000) where
  r0 := (154179621107/250000000000000000)
  k0 := (371263493047267/100000000000000000)
  k6 := (1165546553465133/100000000000000000)
  q := (166144515407521051279/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13802]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13802]

theorem width_13803 : mW 13803 = 308963522557626 := by
  have hu : mW 13803 ≤ 308963522557626 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13803 ≤ 308963522557625 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13803 : RowArithmetic 13803 (565078959957776739629/500000000000000000000000) (611592722340105907352713/1000000000000000000000000) (7589951732764303/1000000000000000000000000) where
  r0 := (308325732797/500000000000000000)
  k0 := (3712433198863773/1000000000000000000)
  k6 := (11655043319312413/1000000000000000000)
  q := (6646021366200984461/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13803]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13803]

theorem width_13804 : mW 13804 = 309041872935196 := by
  have hu : mW 13804 ≤ 309041872935196 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13804 ≤ 309041872935195 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13804 : RowArithmetic 13804 (1130124952870569405673/1000000000000000000000000) (152895255905038739611907/250000000000000000000000) (1517703856211523/200000000000000000000000) where
  r0 := (616584458897/1000000000000000000)
  k0 := (928057873207133/250000000000000000)
  k6 := (5827310574927/500000000000000)
  q := (166156552684508954939/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13804]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13804]

theorem width_13805 : mW 13805 = 309120237503847 := by
  have hu : mW 13805 ≤ 309120237503847 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13805 ≤ 309120237503846 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13805 : RowArithmetic 13805 (565045996914889976513/500000000000000000000000) (611569326597735138975051/1000000000000000000000000) (7587087207184611/1000000000000000000000000) where
  r0 := (308258732167/500000000000000000)
  k0 := (1856014906181043/500000000000000000)
  k6 := (11654199026267783/1000000000000000000)
  q := (83081285497998885983/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13805]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13805]

theorem width_13806 : mW 13806 = 309198616265122 := by
  have hu : mW 13806 ≤ 309198616265122 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13806 ≤ 309198616265121 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13806 : RowArithmetic 13806 (1130059042790640937451/1000000000000000000000000) (611557631272452998425901/1000000000000000000000000) (1517131102203467/200000000000000000000000) where
  r0 := (308225240951/500000000000000000)
  k0 := (371182815745957/100000000000000000)
  k6 := (11653776948545453/1000000000000000000)
  q := (4154214727237868719/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13806]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13806]

theorem width_13807 : mW 13807 = 309277009220561 := by
  have hu : mW 13807 ≤ 309277009220561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13807 ≤ 309277009220560 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13807 : RowArithmetic 13807 (1130026099750611114119/1000000000000000000000000) (12230918752878303191359/20000000000000000000000) (7584224192427963/1000000000000000000000000) where
  r0 := (616383511599/1000000000000000000)
  k0 := (463953316014891/125000000000000000)
  k6 := (2913338729169677/250000000000000000)
  q := (166174606965083567187/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13807]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13807]

theorem width_13808 : mW 13808 = 309355416371708 := by
  have hu : mW 13808 ≤ 309355416371708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13808 ≤ 309355416371707 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13808 : RowArithmetic 13808 (1129993164707147731549/1000000000000000000000000) (122306849142345690883719/200000000000000000000000) (7582793251288627/1000000000000000000000000) where
  r0 := (30815827671/50000000000000000)
  k0 := (3711424924329873/1000000000000000000)
  k6 := (2330586586131849/200000000000000000)
  q := (83090312311363952413/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13808]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13808]

theorem width_13809 : mW 13809 = 309433837720105 := by
  have hu : mW 13809 ≤ 309433837720105 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13809 ≤ 309433837720104 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13809 : RowArithmetic 13809 (1129960237657710341499/1000000000000000000000000) (152880638868874941698653/250000000000000000000000) (7581362687471559/1000000000000000000000000) where
  r0 := (154062401841/250000000000000000)
  k0 := (3711223346092957/1000000000000000000)
  k6 := (5826255495239381/500000000000000000)
  q := (166186642062471434967/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13809]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13809]

theorem width_13810 : mW 13810 = 309512273267294 := by
  have hu : mW 13810 ≤ 309512273267294 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13810 ≤ 309512273267293 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13810 : RowArithmetic 13810 (1129927318599759527923/1000000000000000000000000) (611510866934836154074063/1000000000000000000000000) (151598650016981/20000000000000000000000) where
  r0 := (616182673427/1000000000000000000)
  k0 := (3711021793400499/1000000000000000000)
  k6 := (5826044548064481/500000000000000000)
  q := (20774082410542228327/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13810]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13810]

theorem width_13811 : mW 13811 = 309590723014817 := by
  have hu : mW 13811 ≤ 309590723014817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13811 ≤ 309590723014816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13811 : RowArithmetic 13811 (1129894407530756906429/1000000000000000000000000) (611499180089344825714147/1000000000000000000000000) (7578502691293441/1000000000000000000000000) where
  r0 := (123223150321/200000000000000000)
  k0 := (742164053248923/200000000000000000)
  k6 := (11651667247601549/1000000000000000000)
  q := (83099338144175372247/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13811]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13811]

theorem width_13812 : mW 13812 = 309669186964217 := by
  have hu : mW 13812 ≤ 309669186964217 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13812 ≤ 309669186964216 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13812 : RowArithmetic 13812 (1129861504448164490359/1000000000000000000000000) (305743747469316507596839/500000000000000000000000) (473567078667319/62500000000000000000000) where
  r0 := (77006105237/125000000000000000)
  k0 := (3710618764623443/1000000000000000000)
  k6 := (2912811361222057/250000000000000000)
  q := (166204693074533849037/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13812]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13812]

theorem width_13813 : mW 13813 = 309747665117036 := by
  have hu : mW 13813 ≤ 309747665117036 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13813 ≤ 309747665117035 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13813 : RowArithmetic 13813 (564914304674722978903/500000000000000000000000) (611475811482308132127413/1000000000000000000000000) (757564420287249/100000000000000000000000) where
  r0 := (615981944297/1000000000000000000)
  k0 := (3710417288532107/1000000000000000000)
  k6 := (2912705921995177/250000000000000000)
  q := (415526774107276991/2500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13813]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13813]

theorem width_13814 : mW 13814 = 309826157474817 := by
  have hu : mW 13814 ≤ 309826157474817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13814 ≤ 309826157474816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13814 : RowArithmetic 13814 (564897861116032692027/500000000000000000000000) (611464129719977802340867/1000000000000000000000000) (7574215523752079/1000000000000000000000000) where
  r0 := (153978764701/250000000000000000)
  k0 := (3710215837962719/1000000000000000000)
  k6 := (5825200988435349/500000000000000000)
  q := (20777090749188154807/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13814]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13814]

theorem width_13815 : mW 13815 = 309904664039103 := by
  have hu : mW 13815 ≤ 309904664039103 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13815 ≤ 309904664039102 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13815 : RowArithmetic 13815 (564881421546743937471/500000000000000000000000) (19107889051601550259033/31250000000000000000000) (3786393610594203/500000000000000000000000) where
  r0 := (123169637083/200000000000000000)
  k0 := (3710014412913413/1000000000000000000)
  k6 := (11649980311549911/1000000000000000000)
  q := (83111371063170411399/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13815]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13815]

theorem width_13816 : mW 13816 = 309983184811435 := by
  have hu : mW 13816 ≤ 309983184811435 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13816 ≤ 309983184811434 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13816 : RowArithmetic 13816 (225945994386236166189/200000000000000000000000) (611440771275731334413761/1000000000000000000000000) (1892839823763527/250000000000000000000000) where
  r0 := (615781324127/1000000000000000000)
  k0 := (3709813013379307/1000000000000000000)
  k6 := (11649558692010061/1000000000000000000)
  q := (8311437902072059637/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13816]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13816]

theorem width_13817 : mW 13817 = 310061719793357 := by
  have hu : mW 13817 ≤ 310061719793357 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13817 ≤ 310061719793356 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13817 : RowArithmetic 13817 (1129697108742610783759/1000000000000000000000000) (611429094593030934600321/1000000000000000000000000) (3784965872610901/500000000000000000000000) where
  r0 := (123142894987/200000000000000000)
  k0 := (463701454918687/125000000000000000)
  k6 := (728071069890179/62500000000000000)
  q := (41558693434707496829/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13817]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13817]

theorem width_13818 : mW 13818 = 310140268986412 := by
  have hu : mW 13818 ≤ 310140268986412 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13818 ≤ 310140268986411 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13818 : RowArithmetic 13818 (141208031690655740857/125000000000000000000000) (611417419602756453628501/1000000000000000000000000) (946063071445523/125000000000000000000000) where
  r0 := (615647637839/1000000000000000000)
  k0 := (3709410290828133/1000000000000000000)
  k6 := (291217889756001/25000000000000000)
  q := (83120394609265420643/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13818]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13818]

theorem width_13819 : mW 13819 = 310218832392142 := by
  have hu : mW 13819 ≤ 310218832392142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13819 ≤ 310218832392141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13819 : RowArithmetic 13819 (1129631406276556113617/1000000000000000000000000) (24456229852180640973363/40000000000000000000000) (756707777395403/100000000000000000000000) where
  r0 := (615580812833/1000000000000000000)
  k0 := (231825560487581/62500000000000000)
  k6 := (2912073526998327/250000000000000000)
  q := (166246804480567385131/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13819]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13819]

theorem width_13820 : mW 13820 = 310297410012091 := by
  have hu : mW 13820 ≤ 310297410012091 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13820 ≤ 310297410012090 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13820 : RowArithmetic 13820 (282399641748502740433/250000000000000000000000) (24455762987916718954491/40000000000000000000000) (7565651352264119/1000000000000000000000000) where
  r0 := (153878499979/250000000000000000)
  k0 := (3709007670270123/1000000000000000000)
  k6 := (11647872671494391/1000000000000000000)
  q := (83126409762481622529/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13820]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13820]

theorem width_13821 : mW 13821 = 310376001847800 := by
  have hu : mW 13821 ≤ 310376001847800 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13821 ≤ 310376001847799 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13821 : RowArithmetic 13821 (1129565735675083010203/1000000000000000000000000) (611382404782570676124787/1000000000000000000000000) (3782112653183679/500000000000000000000000) where
  r0 := (153861799771/250000000000000000)
  k0 := (3708806398226713/1000000000000000000)
  k6 := (2329490256147003/200000000000000000)
  q := (83129417175871021501/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13821]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13821]

theorem width_13822 : mW 13822 = 310454607900814 := by
  have hu : mW 13822 ≤ 310454607900814 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13822 ≤ 310454607900813 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13822 : RowArithmetic 13822 (225906582463448659969/200000000000000000000000) (611370736558082677024469/1000000000000000000000000) (236337488629269/31250000000000000000000) where
  r0 := (307690205167/500000000000000000)
  k0 := (452710589803/122070312500000)
  k6 := (2329405987141381/200000000000000000)
  q := (83132424480463698311/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13822]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13822]

theorem width_13823 : mW 13823 = 310533228172675 := by
  have hu : mW 13823 ≤ 310533228172675 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13823 ≤ 310533228172674 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13823 : RowArithmetic 13823 (1129500096917965791177/1000000000000000000000000) (1194060683640747338873/1953125000000000000000) (3780687170722431/500000000000000000000000) where
  r0 := (615313633663/1000000000000000000)
  k0 := (1854201965291811/500000000000000000)
  k6 := (90989129971889/7812500000000000)
  q := (41567715838135729827/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13823]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13823]

theorem width_13824 : mW 13824 = 310611862664926 := by
  have hu : mW 13824 ≤ 310611862664926 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13824 ≤ 310611862664925 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13824 : RowArithmetic 13824 (56473364473736241959/50000000000000000000000) (611347405180119365038451/1000000000000000000000000) (7559949422165137/1000000000000000000000000) where
  r0 := (615246869069/1000000000000000000)
  k0 := (3708202734977169/1000000000000000000)
  k6 := (2329237476562281/200000000000000000)
  q := (166276877526612220179/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13824]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13824]

theorem width_13825 : mW 13825 = 310690511379110 := by
  have hu : mW 13825 ≤ 310690511379110 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13825 ≤ 310690511379109 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13825 : RowArithmetic 13825 (1129434489984995824003/1000000000000000000000000) (611335742025861740359963/1000000000000000000000000) (3779262439085253/500000000000000000000000) where
  r0 := (615180116547/1000000000000000000)
  k0 := (463500195604487/125000000000000000)
  k6 := (11645766174927479/1000000000000000000)
  q := (166282891483158904083/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13825]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13825]

theorem width_13826 : mW 13826 = 310769174316772 := by
  have hu : mW 13826 ≤ 310769174316772 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13826 ≤ 310769174316771 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13826 : RowArithmetic 13826 (1129401698446253891131/1000000000000000000000000) (611324080560898785250269/1000000000000000000000000) (7557100709334049/1000000000000000000000000) where
  r0 := (123022675219/200000000000000000)
  k0 := (3707800420157921/1000000000000000000)
  k6 := (2911336253185437/250000000000000000)
  q := (166288905222206571601/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13826]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13826]

theorem width_13827 : mW 13827 = 310847851479453 := by
  have hu : mW 13827 ≤ 310847851479453 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13827 ≤ 310847851479452 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13827 : RowArithmetic 13827 (1129368914855977729793/1000000000000000000000000) (305656210392419867723939/500000000000000000000000) (3777838457764497/500000000000000000000000) where
  r0 := (61504664771/100000000000000000)
  k0 := (741519860187669/200000000000000000)
  k6 := (232898477924919/20000000000000000)
  q := (166294918743778819047/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13827]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13827]

theorem width_13828 : mW 13828 = 310926542868697 := by
  have hu : mW 13828 ≤ 310926542868697 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13828 ≤ 310926542868696 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13828 : RowArithmetic 13828 (11293361392116451633/10000000000000000000000) (611300762697293742145067/1000000000000000000000000) (7554253496628551/1000000000000000000000000) where
  r0 := (153744982847/250000000000000000)
  k0 := (741479641433851/200000000000000000)
  k6 := (727781426589489/62500000000000000)
  q := (83150466023949619233/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13828]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13828]

theorem width_13829 : mW 13829 = 311005248486047 := by
  have hu : mW 13829 ≤ 311005248486047 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13829 ≤ 311005248486046 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13829 : RowArithmetic 13829 (564651685755367833949/500000000000000000000000) (305644553148935152793071/500000000000000000000000) (7552830452506007/1000000000000000000000000) where
  r0 := (76864153391/125000000000000000)
  k0 := (3707197138851777/1000000000000000000)
  k6 := (11644081800291113/1000000000000000000)
  q := (166306945134591417641/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13829]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13829]

theorem width_13830 : mW 13830 = 311083968333048 := by
  have hu : mW 13830 ≤ 311083968333048 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13830 ≤ 311083968333047 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13830 : RowArithmetic 13830 (1129270611750728485143/1000000000000000000000000) (611277451586178966826539/1000000000000000000000000) (235981493219833/31250000000000000000000) where
  r0 := (24593861397/40000000000000000)
  k0 := (3706996095974981/1000000000000000000)
  k6 := (5821830410407779/500000000000000000)
  q := (166312958003878940089/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13830]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13830]

theorem width_13831 : mW 13831 = 311162702411242 := by
  have hu : mW 13831 ≤ 311162702411242 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13831 ≤ 311162702411241 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13831 : RowArithmetic 13831 (1129237859929105765623/1000000000000000000000000) (76408224820228658782589/125000000000000000000000) (3774992744043959/500000000000000000000000) where
  r0 := (76847481847/125000000000000000)
  k0 := (1853397539266981/500000000000000000)
  k6 := (11643239886996907/1000000000000000000)
  q := (33263794131157077013/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13831]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13831]

theorem width_13832 : mW 13832 = 311241450722174 := by
  have hu : mW 13832 ≤ 311241450722174 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13832 ≤ 311241450722173 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13832 : RowArithmetic 13832 (282301279010837199027/250000000000000000000000) (611254147224431112734827/1000000000000000000000000) (7548563567539191/1000000000000000000000000) where
  r0 := (614713186679/1000000000000000000)
  k0 := (926648521631707/250000000000000000)
  k6 := (11642818998826907/1000000000000000000)
  q := (83162491545167163781/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13832]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13832]

theorem width_13833 : mW 13833 = 311320213267386 := by
  have hu : mW 13833 ≤ 311320213267386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13833 ≤ 311320213267385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13833 : RowArithmetic 13833 (564586190045470884871/500000000000000000000000) (305621248786797167661691/500000000000000000000000) (1886785505315501/250000000000000000000000) where
  r0 := (614646530631/1000000000000000000)
  k0 := (28956196249599/7812500000000000)
  k6 := (2910599539074327/250000000000000000)
  q := (166330995307549338311/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13833]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13833]

theorem width_13834 : mW 13834 = 311398990048422 := by
  have hu : mW 13834 ≤ 311398990048422 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13834 ≤ 311398990048421 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13834 : RowArithmetic 13834 (1129139652069368643893/1000000000000000000000000) (305615424804464485154761/500000000000000000000000) (3772860424564943/500000000000000000000000) where
  r0 := (153644971657/250000000000000000)
  k0 := (370619217879157/100000000000000000)
  k6 := (11641977359399861/1000000000000000000)
  q := (20792125913431747973/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13834]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13834]

theorem width_13835 : mW 13835 = 311477781066826 := by
  have hu : mW 13835 ≤ 311477781066826 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13835 ≤ 311477781066825 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13835 : RowArithmetic 13835 (1129106931976114396801/1000000000000000000000000) (152804800832511297379953/250000000000000000000000) (7544300051016423/1000000000000000000000000) where
  r0 := (153628313667/250000000000000000)
  k0 := (29647930104429/8000000000000000)
  k6 := (5820778304063161/500000000000000000)
  q := (83171509545035913097/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13835]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13835]

theorem width_13836 : mW 13836 = 311556586324142 := by
  have hu : mW 13836 ≤ 311556586324142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13836 ≤ 311556586324141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13836 : RowArithmetic 13836 (141134277476083128379/125000000000000000000000) (305603779368276609171003/500000000000000000000000) (3771439813397627/500000000000000000000000) where
  r0 := (614446634747/1000000000000000000)
  k0 := (370579037272691/100000000000000000)
  k6 := (2328227180493689/200000000000000000)
  q := (83174515327713211749/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13836]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13836]

theorem width_13837 : mW 13837 = 311635405821913 := by
  have hu : mW 13837 ≤ 311635405821913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13837 ≤ 311635405821912 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13837 : RowArithmetic 13837 (1129041515564508179687/1000000000000000000000000) (24447836633122537097631/40000000000000000000000) (1508291915268019/200000000000000000000000) where
  r0 := (307190013431/500000000000000000)
  k0 := (3705589507806511/1000000000000000000)
  k6 := (1164071524241799/100000000000000000)
  q := (83177521001770664697/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13837]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13837]

theorem width_13838 : mW 13838 = 311714239561684 := by
  have hu : mW 13838 ≤ 311714239561684 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13838 ≤ 311714239561683 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13838 : RowArithmetic 13838 (1129008819241131265131/1000000000000000000000000) (152796068651046602406919/250000000000000000000000) (3770019949762333/500000000000000000000000) where
  r0 := (614313431011/1000000000000000000)
  k0 := (115793395884079/31250000000000000)
  k6 := (11640294627966717/1000000000000000000)
  q := (6654442125377603733/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13838]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13838]

theorem width_13839 : mW 13839 = 311793087544999 := by
  have hu : mW 13839 ≤ 311793087544999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13839 ≤ 311793087544998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13839 : RowArithmetic 13839 (28224403270900583493/25000000000000000000000) (30558631753226638712639/50000000000000000000000) (7538620596222767/1000000000000000000000000) where
  r0 := (61424684719/100000000000000000)
  k0 := (926296963542757/250000000000000000)
  k6 := (11639874059106387/1000000000000000000)
  q := (83183532024073130241/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13839]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13839]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13765 then ⟨(282854155991376430937/250000000000000000000000), (612038535468862408396663/1000000000000000000000000), (1528933228341377/200000000000000000000000)⟩ else
  if n = 13766 then ⟨(70711459429150089531/62500000000000000000000), (306013385974968398673389/500000000000000000000000), (7643219236998773/1000000000000000000000000)⟩ else
  if n = 13767 then ⟨(282837521467223482249/250000000000000000000000), (612015010143586812893/1000000000000000000000), (7641772715025159/1000000000000000000000000)⟩ else
  if n = 13768 then ⟨(1131316828970400003971/1000000000000000000000000), (612003250049414242683421/1000000000000000000000000), (7640326575656033/1000000000000000000000000)⟩ else
  if n = 13769 then ⟨(1131283580168340082799/1000000000000000000000000), (152997872916755235790671/250000000000000000000000), (3819440409380771/500000000000000000000000)⟩ else
  if n = 13770 then ⟨(141406292432516632717/125000000000000000000000), (152994933749002224784673/250000000000000000000000), (1527487088842357/200000000000000000000000)⟩ else
  if n = 13771 then ⟨(226243421368640293681/200000000000000000000000), (611967980035980254270877/1000000000000000000000000), (381799522593851/50000000000000000000000)⟩ else
  if n = 13772 then ⟨(565591941157482829101/500000000000000000000000), (305978113393268650270439/500000000000000000000000), (7634545841627433/1000000000000000000000000)⟩ else
  if n = 13773 then ⟨(1131150665872850903501/1000000000000000000000000), (611944475247282405378939/1000000000000000000000000), (1526620322666683/200000000000000000000000)⟩ else
  if n = 13774 then ⟨(1131117457514279661349/1000000000000000000000000), (611932725417818104947043/1000000000000000000000000), (3815828883432631/500000000000000000000000)⟩ else
  if n = 13775 then ⟨(565542128618339007339/500000000000000000000000), (24476839091909881239481/40000000000000000000000), (7630214302093427/1000000000000000000000000)⟩ else
  if n = 13776 then ⟨(1131051065037471807781/1000000000000000000000000), (305954615443335958940551/500000000000000000000000), (3814385609444183/500000000000000000000000)⟩ else
  if n = 13777 then ⟨(1131017880914088576933/1000000000000000000000000), (611897486184195690615551/1000000000000000000000000), (953416064640077/125000000000000000000000)⟩ else
  if n = 13778 then ⟨(141373088107994613241/125000000000000000000000), (611885743189921383863333/1000000000000000000000000), (7625886196660769/1000000000000000000000000)⟩ else
  if n = 13779 then ⟨(565475768442252570499/500000000000000000000000), (305937000951726052611019/500000000000000000000000), (7624444257379421/1000000000000000000000000)⟩ else
  if n = 13780 then ⟨(1130918376973163960963/1000000000000000000000000), (38241391395274450008551/62500000000000000000000), (304920107965891/40000000000000000000000)⟩ else
  if n = 13781 then ⟨(1130885225127365090517/1000000000000000000000000), (152962631113085497639261/250000000000000000000000), (7621561521835087/1000000000000000000000000)⟩ else
  if n = 13782 then ⟨(226170416268908003353/200000000000000000000000), (76479848535863511627813/125000000000000000000000), (7620120725313619/1000000000000000000000000)⟩ else
  if n = 13783 then ⟨(565409472811061278061/500000000000000000000000), (611827053827693025925557/1000000000000000000000000), (952335038681717/125000000000000000000000)⟩ else
  if n = 13784 then ⟨(565392908978773464157/500000000000000000000000), (24472612842972028610639/40000000000000000000000), (7617240274126337/1000000000000000000000000)⟩ else
  if n = 13785 then ⟨(1130752698348248397823/1000000000000000000000000), (611803590026334985371483/1000000000000000000000000), (7615800619202371/1000000000000000000000000)⟩ else
  if n = 13786 then ⟨(1130719586791663273341/1000000000000000000000000), (152947965170849969471641/250000000000000000000000), (1522872268910569/200000000000000000000000)⟩ else
  if n = 13787 then ⟨(1130686483285228907219/1000000000000000000000000), (611780133045099567380271/1000000000000000000000000), (380646122502441/50000000000000000000000)⟩ else
  if n = 13788 then ⟨(4522613551305537339/4000000000000000000000), (611768407111038295041747/1000000000000000000000000), (1522296787112287/200000000000000000000000)⟩ else
  if n = 13789 then ⟨(282655075103141928507/250000000000000000000000), (611756682880820541377753/1000000000000000000000000), (1902511450240453/250000000000000000000000)⟩ else
  if n = 13790 then ⟨(226117444208243905181/200000000000000000000000), (611744960354050813537517/1000000000000000000000000), (304344321844847/40000000000000000000000)⟩ else
  if n = 13791 then ⟨(565277074854890965859/500000000000000000000000), (152933309882583426081113/250000000000000000000000), (760717067091083/100000000000000000000000)⟩ else
  if n = 13792 then ⟨(565260543207848746947/500000000000000000000000), (24468860816370963734693/40000000000000000000000), (7605733675202109/1000000000000000000000000)⟩ else
  if n = 13793 then ⟨(1130488031156407899799/1000000000000000000000000), (305854901495238433846771/500000000000000000000000), (7604297058866327/1000000000000000000000000)⟩ else
  if n = 13794 then ⟨(1130454983929359709117/1000000000000000000000000), (611698087273547046137649/1000000000000000000000000), (7602860821775003/1000000000000000000000000)⟩ else
  if n = 13795 then ⟨(1130421944731996051997/1000000000000000000000000), (611686373258089828031273/1000000000000000000000000), (1520284992759907/200000000000000000000000)⟩ else
  if n = 13796 then ⟨(1130388913561765565329/1000000000000000000000000), (152918665235927611238577/250000000000000000000000), (151999789696231/20000000000000000000000)⟩ else
  if n = 13797 then ⟨(1130355890416114096553/1000000000000000000000000), (611662950330014367171553/1000000000000000000000000), (7598554384682581/1000000000000000000000000)⟩ else
  if n = 13798 then ⟨(565161437646245222689/500000000000000000000000), (611651241416607095536163/1000000000000000000000000), (7597119663284289/1000000000000000000000000)⟩ else
  if n = 13799 then ⟨(282572467047085952937/250000000000000000000000), (611639534203094343448113/1000000000000000000000000), (1519137064097673/200000000000000000000000)⟩ else
  if n = 13800 then ⟨(1130256869101125069831/1000000000000000000000000), (152906957172270468211811/250000000000000000000000), (379712567808329/50000000000000000000000)⟩ else
  if n = 13801 then ⟨(1130223878028285493481/1000000000000000000000000), (611616124874175575680581/1000000000000000000000000), (7592817770190733/1000000000000000000000000)⟩ else
  if n = 13802 then ⟨(1130190894967277393089/1000000000000000000000000), (305802211378990770525657/500000000000000000000000), (7591384562432679/1000000000000000000000000)⟩ else
  if n = 13803 then ⟨(565078959957776739629/500000000000000000000000), (611592722340105907352713/1000000000000000000000000), (7589951732764303/1000000000000000000000000)⟩ else
  if n = 13804 then ⟨(1130124952870569405673/1000000000000000000000000), (152895255905038739611907/250000000000000000000000), (1517703856211523/200000000000000000000000)⟩ else
  if n = 13805 then ⟨(565045996914889976513/500000000000000000000000), (611569326597735138975051/1000000000000000000000000), (7587087207184611/1000000000000000000000000)⟩ else
  if n = 13806 then ⟨(1130059042790640937451/1000000000000000000000000), (611557631272452998425901/1000000000000000000000000), (1517131102203467/200000000000000000000000)⟩ else
  if n = 13807 then ⟨(1130026099750611114119/1000000000000000000000000), (12230918752878303191359/20000000000000000000000), (7584224192427963/1000000000000000000000000)⟩ else
  if n = 13808 then ⟨(1129993164707147731549/1000000000000000000000000), (122306849142345690883719/200000000000000000000000), (7582793251288627/1000000000000000000000000)⟩ else
  if n = 13809 then ⟨(1129960237657710341499/1000000000000000000000000), (152880638868874941698653/250000000000000000000000), (7581362687471559/1000000000000000000000000)⟩ else
  if n = 13810 then ⟨(1129927318599759527923/1000000000000000000000000), (611510866934836154074063/1000000000000000000000000), (151598650016981/20000000000000000000000)⟩ else
  if n = 13811 then ⟨(1129894407530756906429/1000000000000000000000000), (611499180089344825714147/1000000000000000000000000), (7578502691293441/1000000000000000000000000)⟩ else
  if n = 13812 then ⟨(1129861504448164490359/1000000000000000000000000), (305743747469316507596839/500000000000000000000000), (473567078667319/62500000000000000000000)⟩ else
  if n = 13813 then ⟨(564914304674722978903/500000000000000000000000), (611475811482308132127413/1000000000000000000000000), (757564420287249/100000000000000000000000)⟩ else
  if n = 13814 then ⟨(564897861116032692027/500000000000000000000000), (611464129719977802340867/1000000000000000000000000), (7574215523752079/1000000000000000000000000)⟩ else
  if n = 13815 then ⟨(564881421546743937471/500000000000000000000000), (19107889051601550259033/31250000000000000000000), (3786393610594203/500000000000000000000000)⟩ else
  if n = 13816 then ⟨(225945994386236166189/200000000000000000000000), (611440771275731334413761/1000000000000000000000000), (1892839823763527/250000000000000000000000)⟩ else
  if n = 13817 then ⟨(1129697108742610783759/1000000000000000000000000), (611429094593030934600321/1000000000000000000000000), (3784965872610901/500000000000000000000000)⟩ else
  if n = 13818 then ⟨(141208031690655740857/125000000000000000000000), (611417419602756453628501/1000000000000000000000000), (946063071445523/125000000000000000000000)⟩ else
  if n = 13819 then ⟨(1129631406276556113617/1000000000000000000000000), (24456229852180640973363/40000000000000000000000), (756707777395403/100000000000000000000000)⟩ else
  if n = 13820 then ⟨(282399641748502740433/250000000000000000000000), (24455762987916718954491/40000000000000000000000), (7565651352264119/1000000000000000000000000)⟩ else
  if n = 13821 then ⟨(1129565735675083010203/1000000000000000000000000), (611382404782570676124787/1000000000000000000000000), (3782112653183679/500000000000000000000000)⟩ else
  if n = 13822 then ⟨(225906582463448659969/200000000000000000000000), (611370736558082677024469/1000000000000000000000000), (236337488629269/31250000000000000000000)⟩ else
  if n = 13823 then ⟨(1129500096917965791177/1000000000000000000000000), (1194060683640747338873/1953125000000000000000), (3780687170722431/500000000000000000000000)⟩ else
  if n = 13824 then ⟨(56473364473736241959/50000000000000000000000), (611347405180119365038451/1000000000000000000000000), (7559949422165137/1000000000000000000000000)⟩ else
  if n = 13825 then ⟨(1129434489984995824003/1000000000000000000000000), (611335742025861740359963/1000000000000000000000000), (3779262439085253/500000000000000000000000)⟩ else
  if n = 13826 then ⟨(1129401698446253891131/1000000000000000000000000), (611324080560898785250269/1000000000000000000000000), (7557100709334049/1000000000000000000000000)⟩ else
  if n = 13827 then ⟨(1129368914855977729793/1000000000000000000000000), (305656210392419867723939/500000000000000000000000), (3777838457764497/500000000000000000000000)⟩ else
  if n = 13828 then ⟨(11293361392116451633/10000000000000000000000), (611300762697293742145067/1000000000000000000000000), (7554253496628551/1000000000000000000000000)⟩ else
  if n = 13829 then ⟨(564651685755367833949/500000000000000000000000), (305644553148935152793071/500000000000000000000000), (7552830452506007/1000000000000000000000000)⟩ else
  if n = 13830 then ⟨(1129270611750728485143/1000000000000000000000000), (611277451586178966826539/1000000000000000000000000), (235981493219833/31250000000000000000000)⟩ else
  if n = 13831 then ⟨(1129237859929105765623/1000000000000000000000000), (76408224820228658782589/125000000000000000000000), (3774992744043959/500000000000000000000000)⟩ else
  if n = 13832 then ⟨(282301279010837199027/250000000000000000000000), (611254147224431112734827/1000000000000000000000000), (7548563567539191/1000000000000000000000000)⟩ else
  if n = 13833 then ⟨(564586190045470884871/500000000000000000000000), (305621248786797167661691/500000000000000000000000), (1886785505315501/250000000000000000000000)⟩ else
  if n = 13834 then ⟨(1129139652069368643893/1000000000000000000000000), (305615424804464485154761/500000000000000000000000), (3772860424564943/500000000000000000000000)⟩ else
  if n = 13835 then ⟨(1129106931976114396801/1000000000000000000000000), (152804800832511297379953/250000000000000000000000), (7544300051016423/1000000000000000000000000)⟩ else
  if n = 13836 then ⟨(141134277476083128379/125000000000000000000000), (305603779368276609171003/500000000000000000000000), (3771439813397627/500000000000000000000000)⟩ else
  if n = 13837 then ⟨(1129041515564508179687/1000000000000000000000000), (24447836633122537097631/40000000000000000000000), (1508291915268019/200000000000000000000000)⟩ else
  if n = 13838 then ⟨(1129008819241131265131/1000000000000000000000000), (152796068651046602406919/250000000000000000000000), (3770019949762333/500000000000000000000000)⟩ else
  ⟨(28224403270900583493/25000000000000000000000), (30558631753226638712639/50000000000000000000000), (7538620596222767/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13765 ≤ n) (hb : n ≤ 13839) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13765
  · exact row_13766
  · exact row_13767
  · exact row_13768
  · exact row_13769
  · exact row_13770
  · exact row_13771
  · exact row_13772
  · exact row_13773
  · exact row_13774
  · exact row_13775
  · exact row_13776
  · exact row_13777
  · exact row_13778
  · exact row_13779
  · exact row_13780
  · exact row_13781
  · exact row_13782
  · exact row_13783
  · exact row_13784
  · exact row_13785
  · exact row_13786
  · exact row_13787
  · exact row_13788
  · exact row_13789
  · exact row_13790
  · exact row_13791
  · exact row_13792
  · exact row_13793
  · exact row_13794
  · exact row_13795
  · exact row_13796
  · exact row_13797
  · exact row_13798
  · exact row_13799
  · exact row_13800
  · exact row_13801
  · exact row_13802
  · exact row_13803
  · exact row_13804
  · exact row_13805
  · exact row_13806
  · exact row_13807
  · exact row_13808
  · exact row_13809
  · exact row_13810
  · exact row_13811
  · exact row_13812
  · exact row_13813
  · exact row_13814
  · exact row_13815
  · exact row_13816
  · exact row_13817
  · exact row_13818
  · exact row_13819
  · exact row_13820
  · exact row_13821
  · exact row_13822
  · exact row_13823
  · exact row_13824
  · exact row_13825
  · exact row_13826
  · exact row_13827
  · exact row_13828
  · exact row_13829
  · exact row_13830
  · exact row_13831
  · exact row_13832
  · exact row_13833
  · exact row_13834
  · exact row_13835
  · exact row_13836
  · exact row_13837
  · exact row_13838
  · exact row_13839

end BstLean.Part271.R3.Rows13765
