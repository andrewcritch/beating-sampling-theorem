import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13925–13999. -/
namespace BstLean.Part271.R3.Rows13925
open Real BstLean.Part130 BstLean.Part227

theorem width_13925 : mW 13925 = 318627468766844 := by
  have hu : mW 13925 ≤ 318627468766844 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13925 ≤ 318627468766843 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13925 : RowArithmetic 13925 (281548569271995555697/250000000000000000000000) (610177892906420748115821/1000000000000000000000000) (7417944103759921/1000000000000000000000000) where
  r0 := (608565312183/1000000000000000000)
  k0 := (922003075079269/250000000000000000)
  k6 := (1450484349242269/125000000000000000)
  q := (41720798170696590833/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13925]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13925]

theorem width_13926 : mW 13926 = 318707561854934 := by
  have hu : mW 13926 ≤ 318707561854934 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13926 ≤ 318707561854933 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13926 : RowArithmetic 13926 (1126162268071127789541/1000000000000000000000000) (30508319920881161854583/50000000000000000000000) (7416556818890647/1000000000000000000000000) where
  r0 := (121699952691/200000000000000000)
  k0 := (3687813676586611/1000000000000000000)
  k6 := (11603458160191399/1000000000000000000)
  q := (166889184790387181039/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13926]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13926]

theorem width_13927 : mW 13927 = 318787669322651 := by
  have hu : mW 13927 ≤ 318787669322651 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13927 ≤ 318787669322650 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13927 : RowArithmetic 13927 (1126130266755382563207/1000000000000000000000000) (305077452789631505975677/500000000000000000000000) (7415169896630237/1000000000000000000000000) where
  r0 := (304217113247/500000000000000000)
  k0 := (1843807538908339/500000000000000000)
  k6 := (2320608314263753/200000000000000000)
  q := (33379035336570168771/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13927]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13927]

theorem width_13928 : mW 13928 = 318867791171545 := by
  have hu : mW 13928 ≤ 318867791171545 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13928 ≤ 318867791171544 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13928 : RowArithmetic 13928 (56304913656916035501/50000000000000000000000) (305071707195480750337811/500000000000000000000000) (1853445834214249/250000000000000000000000) where
  r0 := (38023043831/62500000000000000)
  k0 := (3687416503999189/1000000000000000000)
  k6 := (11602625027312193/1000000000000000000)
  q := (83450584180100261297/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13928]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13928]

theorem width_13929 : mW 13929 = 318947927403165 := by
  have hu : mW 13929 ≤ 318947927403165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13929 ≤ 318947927403164 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13929 : RowArithmetic 13929 (1126066287217517977227/1000000000000000000000000) (610131924852340205896837/1000000000000000000000000) (7412397139449307/1000000000000000000000000) where
  r0 := (304151593929/500000000000000000)
  k0 := (921804488782271/250000000000000000)
  k6 := (725138033010227/62500000000000000)
  q := (166907159822459383913/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13929]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13929]

theorem width_13930 : mW 13930 = 319028078019059 := by
  have hu : mW 13930 ≤ 319028078019059 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13930 ≤ 319028078019058 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13930 : RowArithmetic 13930 (563017154495275845657/500000000000000000000000) (122024087392604171693849/200000000000000000000000) (11857618086857/1600000000000000000000) where
  r0 := (304118843089/500000000000000000)
  k0 := (368701943120433/100000000000000000)
  k6 := (1160179207386503/100000000000000000)
  q := (16691315106965059031/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13930]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13930]

theorem width_13931 : mW 13931 = 319108243020776 := by
  have hu : mW 13931 ≤ 319108243020776 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13931 ≤ 319108243020775 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13931 : RowArithmetic 13931 (140750292306874943909/125000000000000000000000) (610108950722625173783421/1000000000000000000000000) (7409625831244433/1000000000000000000000000) where
  r0 := (152043049063/250000000000000000)
  k0 := (1843410466108417/500000000000000000)
  k6 := (11601375664408339/1000000000000000000)
  q := (83459571050898650063/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13931]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13931]

theorem width_13932 : mW 13932 = 319188422409866 := by
  have hu : mW 13932 ≤ 319188422409866 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13932 ≤ 319188422409865 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13932 : RowArithmetic 13932 (22519407512168792587/20000000000000000000000) (122019493226155019502199/200000000000000000000000) (3704120360102121/500000000000000000000000) where
  r0 := (304053359039/500000000000000000)
  k0 := (46082780727057/12500000000000000)
  k6 := (11600959299785511/1000000000000000000)
  q := (83462566459461333773/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13932]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13932]

theorem width_13933 : mW 13933 = 319268616187878 := by
  have hu : mW 13933 ≤ 319268616187878 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13933 ≤ 319268616187877 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13933 : RowArithmetic 13933 (140742302556056446971/125000000000000000000000) (610085983187092682955483/1000000000000000000000000) (3703427985521819/500000000000000000000000) where
  r0 := (152010312913/250000000000000000)
  k0 := (3686424009039411/1000000000000000000)
  k6 := (1450067872498563/125000000000000000)
  q := (166931123521049842601/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13933]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13933]

theorem width_13934 : mW 13934 = 319348824356361 := by
  have hu : mW 13934 ≤ 319348824356361 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13934 ≤ 319348824356360 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13934 : RowArithmetic 13934 (56295323648630800761/50000000000000000000000) (122014900378240000827961/200000000000000000000000) (3702735791820629/500000000000000000000000) where
  r0 := (151993949243/250000000000000000)
  k0 := (3686225584839349/1000000000000000000)
  k6 := (1450015838126159/125000000000000000)
  q := (5216784809631311599/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13934]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13934]

theorem width_13935 : mW 13935 = 319429046916864 := by
  have hu : mW 13935 ≤ 319429046916864 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13935 ≤ 319429046916863 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13935 : RowArithmetic 13935 (17591789580914289787/15625000000000000000000) (610063022242719311107959/1000000000000000000000000) (1851021889468947/250000000000000000000000) where
  r0 := (121582070807/200000000000000000)
  k0 := (737205437111861/200000000000000000)
  k6 := (11599710474839777/1000000000000000000)
  q := (166943104080402194971/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13935]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13935]

theorem width_13936 : mW 13936 = 319509283870937 := by
  have hu : mW 13936 ≤ 319509283870937 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13936 ≤ 319509283870936 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13936 : RowArithmetic 13936 (1125842601063729140113/1000000000000000000000000) (6100515442412730651181/10000000000000000000000) (7402703893625943/1000000000000000000000000) where
  r0 := (607844922837/1000000000000000000)
  k0 := (147433152447647/40000000000000000)
  k6 := (579964714473599/50000000000000000)
  q := (166949094037673651583/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13936]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13936]

theorem width_13937 : mW 13937 = 319589535220128 := by
  have hu : mW 13937 ≤ 319589535220128 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13937 ≤ 319589535220127 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13937 : RowArithmetic 13937 (1125810676625843943263/1000000000000000000000000) (610040067886483749363961/1000000000000000000000000) (7401320590770537/1000000000000000000000000) where
  r0 := (37986218961/62500000000000000)
  k0 := (1842815230866459/500000000000000000)
  k6 := (11598878148897843/1000000000000000000)
  q := (6678203351201578977/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13937]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13937]

theorem width_13938 : mW 13938 = 319669800965989 := by
  have hu : mW 13938 ≤ 319669800965989 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13938 ≤ 319669800965988 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13938 : RowArithmetic 13938 (1125778759862441671181/1000000000000000000000000) (305014296588986962473067/500000000000000000000000) (7399937649188339/1000000000000000000000000) where
  r0 := (18991065489/31250000000000000)
  k0 := (3685432137176427/1000000000000000000)
  k6 := (2899615513277333/250000000000000000)
  q := (16696107330752279277/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13938]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13938]

theorem width_13939 : mW 13939 = 319750081110067 := by
  have hu : mW 13939 ≤ 319750081110067 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13939 ≤ 319750081110066 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13939 : RowArithmetic 13939 (1125746850771109016549/1000000000000000000000000) (61001712011536633679219/100000000000000000000000) (462409691797393/62500000000000000000000) where
  r0 := (151912174913/250000000000000000)
  k0 := (3685233837522689/1000000000000000000)
  k6 := (2319609200419683/200000000000000000)
  q := (83483531310073365871/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13939]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13939]

theorem width_13940 : mW 13940 = 319830375653912 := by
  have hu : mW 13940 ≤ 319830375653912 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13940 ≤ 319830375653911 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13940 : RowArithmetic 13940 (225142989869886368163/200000000000000000000000) (610005648698283890042157/1000000000000000000000000) (7397172849359301/1000000000000000000000000) where
  r0 := (75947914423/125000000000000000)
  k0 := (737007112552719/200000000000000000)
  k6 := (11597629995857061/1000000000000000000)
  q := (41743262929483603079/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13940]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13940]

theorem width_13941 : mW 13941 = 319910684599075 := by
  have hu : mW 13941 ≤ 319910684599075 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13941 ≤ 319910684599074 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13941 : RowArithmetic 13941 (1125683055594996377397/1000000000000000000000000) (609994178926349497470597/1000000000000000000000000) (3697895495435163/500000000000000000000000) where
  r0 := (15187948571/25000000000000000)
  k0 := (460604664111379/125000000000000000)
  k6 := (5798607017188621/500000000000000000)
  q := (41744760150227237831/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13941]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13941]

theorem width_13942 : mW 13942 = 319991007947105 := by
  have hu : mW 13942 ≤ 319991007947105 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13942 ≤ 319991007947104 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13942 : RowArithmetic 13942 (1125651169505391031587/1000000000000000000000000) (304991355399593150966939/500000000000000000000000) (1848602373292601/250000000000000000000000) where
  r0 := (303726291009/500000000000000000)
  k0 := (3684639087902953/1000000000000000000)
  k6 := (1159679811765093/100000000000000000)
  q := (3339700585381869229/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13942]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13942]

theorem width_13943 : mW 13943 = 320071345699551 := by
  have hu : mW 13943 ≤ 320071345699551 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13943 ≤ 320071345699550 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13943 : RowArithmetic 13943 (562809645539102589301/500000000000000000000000) (152492811079104367922819/250000000000000000000000) (924128544517329/125000000000000000000000) where
  r0 := (151846808229/250000000000000000)
  k0 := (1842220443898653/500000000000000000)
  k6 := (5798191122835051/500000000000000000)
  q := (166991017722511051233/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13943]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13943]

theorem width_13944 : mW 13944 = 320151697857963 := by
  have hu : mW 13944 ≤ 320151697857963 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13944 ≤ 320151697857962 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13944 : RowArithmetic 13944 (140698427538878570483/125000000000000000000000) (152489944869416589235787/250000000000000000000000) (739164757965413/100000000000000000000000) where
  r0 := (60732189553/100000000000000000)
  k0 := (460530339070747/125000000000000000)
  k6 := (2319193283685347/200000000000000000)
  q := (16699700596118482507/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13944]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13944]

theorem width_13945 : mW 13945 = 320232064423892 := by
  have hu : mW 13945 ≤ 320232064423892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13945 ≤ 320232064423891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13945 : RowArithmetic 13945 (562777778600725651873/500000000000000000000000) (76243539535319548783221/125000000000000000000000) (461891697724753/62500000000000000000000) where
  r0 := (607256569857/1000000000000000000)
  k0 := (3684044562203877/1000000000000000000)
  k6 := (11595550635912809/1000000000000000000)
  q := (10437687124071117701/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13945]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13945]

theorem width_13946 : mW 13946 = 320312445398886 := by
  have hu : mW 13946 ≤ 320312445398886 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13946 ≤ 320312445398885 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13946 : RowArithmetic 13946 (281380925436766570297/250000000000000000000000) (304968427365355567913249/500000000000000000000000) (923610888480457/125000000000000000000000) where
  r0 := (303595627947/500000000000000000)
  k0 := (5756010057353/1562500000000000)
  k6 := (724695931132519/62500000000000000)
  q := (33401796358878664357/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13946]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13946]

theorem width_13947 : mW 13947 = 320392840784497 := by
  have hu : mW 13947 ≤ 320392840784497 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13947 ≤ 320392840784496 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13947 : RowArithmetic 13947 (70343240871591559511/62500000000000000000000) (15248134870543857353087/25000000000000000000000) (7387507412276181/1000000000000000000000000) where
  r0 := (303562976819/500000000000000000)
  k0 := (3683648336067017/1000000000000000000)
  k6 := (2318943841008241/200000000000000000)
  q := (167014969388974232749/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13947]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13947]

theorem width_13948 : mW 13948 = 320473250582273 := by
  have hu : mW 13948 ≤ 320473250582273 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13948 ≤ 320473250582272 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13948 : RowArithmetic 13948 (112546001379424213597/100000000000000000000000) (304956968277654824501151/500000000000000000000000) (3693064038386497/500000000000000000000000) where
  r0 := (607060663087/1000000000000000000)
  k0 := (3683450260285111/1000000000000000000)
  k6 := (11594303556667497/1000000000000000000)
  q := (167020956768903703943/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13948]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13948]

theorem width_13949 : mW 13949 = 320553674793766 := by
  have hu : mW 13949 ≤ 320553674793766 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13949 ≤ 320553674793765 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13949 : RowArithmetic 13949 (1125428181290991225867/1000000000000000000000000) (609902479931001114812069/1000000000000000000000000) (461546818825839/62500000000000000000000) where
  r0 := (606995384237/1000000000000000000)
  k0 := (3683252209352077/1000000000000000000)
  k6 := (181154499265487/15625000000000000)
  q := (83513471967102409531/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13949]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13949]

theorem width_13950 : mW 13950 = 320634113420524 := by
  have hu : mW 13950 ≤ 320634113420524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13950 ≤ 320634113420523 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13950 : RowArithmetic 13950 (1125396356433308975439/1000000000000000000000000) (609891024948452728823467/1000000000000000000000000) (7383370485476943/1000000000000000000000000) where
  r0 := (303465058543/500000000000000000)
  k0 := (1841527091632927/500000000000000000)
  k6 := (11593472394004207/1000000000000000000)
  q := (326236193134571597/1953125000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13950]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13950]

theorem width_13951 : mW 13951 = 320714566464099 := by
  have hu : mW 13951 ≤ 320714566464099 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13951 ≤ 320714566464098 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13951 : RowArithmetic 13951 (281341134804697678321/250000000000000000000000) (609879571607288688306367/1000000000000000000000000) (7381992229442981/1000000000000000000000000) where
  r0 := (606864861631/1000000000000000000)
  k0 := (3682856182021347/1000000000000000000)
  k6 := (5796528439849303/500000000000000000)
  q := (167038917621014295173/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13951]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13951]

theorem width_13952 : mW 13952 = 320795033926041 := by
  have hu : mW 13952 ≤ 320795033926041 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13952 ≤ 320795033926040 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13952 : RowArithmetic 13952 (281333182411258482709/250000000000000000000000) (609868119907133214429873/1000000000000000000000000) (1476122866598213/200000000000000000000000) where
  r0 := (151699904467/250000000000000000)
  k0 := (1841329102805213/500000000000000000)
  k6 := (11592641410066359/1000000000000000000)
  q := (167044904142568802877/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13952]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13952]

theorem width_13953 : mW 13953 = 320875515807899 := by
  have hu : mW 13953 ≤ 320875515807899 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13953 ≤ 320875515807898 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13953 : RowArithmetic 13953 (1125300927709637682391/1000000000000000000000000) (609856669847610698718793/1000000000000000000000000) (1844809199000199/250000000000000000000000) where
  r0 := (303367192897/500000000000000000)
  k0 := (460307531753499/125000000000000000)
  k6 := (579611299254973/50000000000000000)
  q := (20881361306198405991/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13953]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13953]

theorem width_13954 : mW 13954 = 320956012111224 := by
  have hu : mW 13954 ≤ 320956012111224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13954 ≤ 320956012111223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13954 : RowArithmetic 13954 (562634566705100396603/500000000000000000000000) (609845221428345661468941/1000000000000000000000000) (3688929809175889/500000000000000000000000) where
  r0 := (18958411419/31250000000000000)
  k0 := (1841131163637507/500000000000000000)
  k6 := (2897952651197477/250000000000000000)
  q := (41764219135523173337/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13954]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13954]

theorem width_13955 : mW 13955 = 321036522837567 := by
  have hu : mW 13955 ≤ 321036522837567 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13955 ≤ 321036522837566 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13955 : RowArithmetic 13955 (45009493869772922177/40000000000000000000000) (304916887324481364891649/500000000000000000000000) (1844120699980917/250000000000000000000000) where
  r0 := (121320791341/200000000000000000)
  k0 := (1841032212670161/500000000000000000)
  k6 := (5795697634564851/500000000000000000)
  q := (83531431210054099013/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13955]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13955]

theorem width_13956 : mW 13956 = 321117047988478 := by
  have hu : mW 13956 ≤ 321117047988478 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13956 ≤ 321117047988477 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13956 : RowArithmetic 13956 (1125205567709605818807/1000000000000000000000000) (121964465901817331602481/200000000000000000000000) (7375106340596193/1000000000000000000000000) where
  r0 := (151634689921/250000000000000000)
  k0 := (1840933274112441/500000000000000000)
  k6 := (2318195995622169/200000000000000000)
  q := (167068848083656816719/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13956]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13956]

theorem width_13957 : mW 13957 = 321197587565507 := by
  have hu : mW 13957 ≤ 321197587565507 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13957 ≤ 321197587565506 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13957 : RowArithmetic 13957 (1125173796303651402997/1000000000000000000000000) (609810886008342302820599/1000000000000000000000000) (3686865120124567/500000000000000000000000) where
  r0 := (30323678717/50000000000000000)
  k0 := (3681668695917519/1000000000000000000)
  k6 := (5795282365862669/500000000000000000)
  q := (20884354191595200007/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13957]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13957]

theorem width_13958 : mW 13958 = 321278141570205 := by
  have hu : mW 13958 ≤ 321278141570205 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13958 ≤ 321278141570204 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13958 : RowArithmetic 13958 (70321377032753905707/62500000000000000000000) (121959888829270923415349/200000000000000000000000) (7372354498762297/1000000000000000000000000) where
  r0 := (606408400671/1000000000000000000)
  k0 := (3681470868416163/1000000000000000000)
  k6 := (11590149529965189/1000000000000000000)
  q := (20885102345930699317/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13958]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13958]

theorem width_13959 : mW 13959 = 321358710004123 := by
  have hu : mW 13959 ≤ 321358710004123 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13959 ≤ 321358710004122 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13959 : RowArithmetic 13959 (562555138184221365977/500000000000000000000000) (609788003922748688415001/1000000000000000000000000) (3685489558007769/500000000000000000000000) where
  r0 := (24253729547/40000000000000000)
  k0 := (184063653285937/50000000000000000)
  k6 := (2317946874564481/200000000000000000)
  q := (167086803787731842531/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13959]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13959]

theorem width_13960 : mW 13960 = 321439292868812 := by
  have hu : mW 13960 ≤ 321439292868812 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13960 ≤ 321439292868811 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13960 : RowArithmetic 13960 (1125078527834396736511/1000000000000000000000000) (609776565337149806878861/1000000000000000000000000) (7369604091888767/1000000000000000000000000) where
  r0 := (606278088347/1000000000000000000)
  k0 := (460134410976759/125000000000000000)
  k6 := (2317863852057799/200000000000000000)
  q := (83546394296821691143/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13960]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13960]

theorem width_13961 : mW 13961 = 321519890165821 := by
  have hu : mW 13961 ≤ 321519890165821 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13961 ≤ 321519890165820 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13961 : RowArithmetic 13961 (281261696729882817353/250000000000000000000000) (609765128389183255535999/1000000000000000000000000) (1473645885252397/200000000000000000000000) where
  r0 := (303106474843/500000000000000000)
  k0 := (1840438767351559/500000000000000000)
  k6 := (11588904192356971/1000000000000000000)
  q := (167098773185203247919/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13961]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13961]

theorem width_13962 : mW 13962 = 321600501896702 := by
  have hu : mW 13962 ≤ 321600501896702 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13962 ≤ 321600501896701 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13962 : RowArithmetic 13962 (562507526810726135649/500000000000000000000000) (121950738615694899246191/200000000000000000000000) (368342755950759/50000000000000000000000) where
  r0 := (18942119459/31250000000000000)
  k0 := (368067980637773/100000000000000000)
  k6 := (11588489169018347/1000000000000000000)
  q := (83552378781217234713/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13962]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13962]

theorem width_13963 : mW 13963 = 321681128063006 := by
  have hu : mW 13963 ≤ 321681128063006 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13963 ≤ 321681128063005 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13963 : RowArithmetic 13963 (112498332793776724017/100000000000000000000000) (609742259404649061987939/1000000000000000000000000) (920685146253551/125000000000000000000000) where
  r0 := (606082707351/1000000000000000000)
  k0 := (368048210283583/100000000000000000)
  k6 := (5794037095132569/500000000000000000)
  q := (83555370862680036339/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13963]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13963]

theorem width_13964 : mW 13964 = 321761768666283 := by
  have hu : mW 13964 ≤ 321761768666283 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13964 ≤ 321761768666282 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13964 : RowArithmetic 13964 (22499032197321704593/20000000000000000000000) (304865413683666334512303/500000000000000000000000) (7364107579181801/1000000000000000000000000) where
  r0 := (606017603671/1000000000000000000)
  k0 := (3680284424069267/1000000000000000000)
  k6 := (5793829628044681/500000000000000000)
  q := (83558362837001539711/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13964]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13964]

theorem width_13965 : mW 13965 = 321842423708085 := by
  have hu : mW 13965 ≤ 321842423708085 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13965 ≤ 321842423708084 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13965 : RowArithmetic 13965 (1124919899404015065287/1000000000000000000000000) (304859698483075545824769/500000000000000000000000) (920341793294437/125000000000000000000000) where
  r0 := (302976255823/500000000000000000)
  k0 := (3680086770075959/1000000000000000000)
  k6 := (11587244366483039/1000000000000000000)
  q := (83561354704193253643/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13965]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13965]

theorem width_13966 : mW 13966 = 321923093189962 := by
  have hu : mW 13966 ≤ 321923093189962 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13966 ≤ 321923093189961 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13966 : RowArithmetic 13966 (1124888196549167721487/1000000000000000000000000) (609707968200730276632737/1000000000000000000000000) (294454458857189/40000000000000000000000) where
  r0 := (75735928909/125000000000000000)
  k0 := (459986142605969/125000000000000000)
  k6 := (1158682952143819/100000000000000000)
  q := (10445543308033335611/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13966]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13966]

theorem width_13967 : mW 13967 = 322003777113466 := by
  have hu : mW 13967 ≤ 322003777113466 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13967 ≤ 322003777113465 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13967 : RowArithmetic 13967 (562428250649576972289/500000000000000000000000) (609696541070696271680397/1000000000000000000000000) (7359988954284723/1000000000000000000000000) where
  r0 := (151455590637/250000000000000000)
  k0 := (1839845768192799/500000000000000000)
  k6 := (11586414720946839/1000000000000000000)
  q := (83567338117233338139/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13967]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13967]

theorem width_13968 : mW 13968 = 322084475480147 := by
  have hu : mW 13968 ≤ 322084475480147 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13968 ≤ 322084475480146 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13968 : RowArithmetic 13968 (562412406825793313877/500000000000000000000000) (762106394469593993919/1250000000000000000000) (919827099350103/125000000000000000000000) where
  r0 := (605757305469/1000000000000000000)
  k0 := (3679493956678303/1000000000000000000)
  k6 := (2896499991250253/250000000000000000)
  q := (83570329663104716031/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13968]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13968]

theorem width_13969 : mW 13969 = 322165188291557 := by
  have hu : mW 13969 ≤ 322165188291557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13969 ≤ 322165188291556 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13969 : RowArithmetic 13969 (112479313360407843613/100000000000000000000000) (304836845857646674368127/500000000000000000000000) (1839311248214591/250000000000000000000000) where
  r0 := (605692260033/1000000000000000000)
  k0 := (183964820086189/50000000000000000)
  k6 := (362049539174773/31250000000000000)
  q := (83573321101892319139/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13969]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13969]

theorem width_13970 : mW 13970 = 322245915549248 := by
  have hu : mW 13970 ≤ 322245915549248 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13970 ≤ 322245915549247 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13970 : RowArithmetic 13970 (1124761461154242994209/1000000000000000000000000) (304831134744588543881213/500000000000000000000000) (735587354833773/100000000000000000000000) where
  r0 := (605627226237/1000000000000000000)
  k0 := (459887358939613/125000000000000000)
  k6 := (11585170586714041/1000000000000000000)
  q := (4178815621680382299/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13970]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13970]

theorem width_13971 : mW 13971 = 322326657254769 := by
  have hu : mW 13971 ≤ 322326657254769 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13971 ≤ 322326657254768 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13971 : RowArithmetic 13971 (281182449074924165721/250000000000000000000000) (609650848896952921907599/1000000000000000000000000) (7354502461119427/1000000000000000000000000) where
  r0 := (302781102039/500000000000000000)
  k0 := (919725341513137/250000000000000000)
  k6 := (5792377982178479/500000000000000000)
  q := (41789651829131096507/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13971]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13971]

theorem width_13972 : mW 13972 = 322407413409673 := by
  have hu : mW 13972 ≤ 322407413409673 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13972 ≤ 322407413409672 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13972 : RowArithmetic 13972 (562349069519027194733/500000000000000000000000) (304819714969123741239589/500000000000000000000000) (7353131731083921/1000000000000000000000000) where
  r0 := (605497193553/1000000000000000000)
  k0 := (735740777065117/200000000000000000)
  k6 := (5792170693256761/500000000000000000)
  q := (167164589551734909287/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13972]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13972]

theorem width_13973 : mW 13973 = 322488184015512 := by
  have hu : mW 13973 ≤ 322488184015512 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13973 ≤ 322488184015511 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13973 : RowArithmetic 13973 (224933297873386534431/200000000000000000000000) (76203501576585939684639/125000000000000000000000) (3675880679055873/500000000000000000000000) where
  r0 := (605432194659/1000000000000000000)
  k0 := (735701285866177/200000000000000000)
  k6 := (11583926853175767/1000000000000000000)
  q := (41792642893217461607/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13973]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13973]

theorem width_13974 : mW 13974 = 322568969073835 := by
  have hu : mW 13974 ≤ 322568969073835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13974 ≤ 322568969073834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13974 : RowArithmetic 13974 (1124634847283950741831/1000000000000000000000000) (76202074614987485834379/125000000000000000000000) (7350391342083561/1000000000000000000000000) where
  r0 := (302683603697/500000000000000000)
  k0 := (1839154499033177/500000000000000000)
  k6 := (2895878091083933/250000000000000000)
  q := (16717655337995217803/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13974]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13974]

theorem width_13975 : mW 13975 = 322649768586196 := by
  have hu : mW 13975 ≤ 322649768586196 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13975 ≤ 322649768586195 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13975 : RowArithmetic 13975 (562301606393362912877/500000000000000000000000) (76200647857438944051289/125000000000000000000000) (1469804336575991/200000000000000000000000) where
  r0 := (302651115877/500000000000000000)
  k0 := (1839055795761911/500000000000000000)
  k6 := (723943619999091/62500000000000000)
  q := (83591267486502440281/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13975]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13975]

theorem width_13976 : mW 13976 = 322730582554145 := by
  have hu : mW 13976 ≤ 322730582554145 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13976 ≤ 322730582554144 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13976 : RowArithmetic 13976 (281142896468219618657/250000000000000000000000) (304796885215574773679401/500000000000000000000000) (3673826190190831/500000000000000000000000) where
  r0 := (605237267737/1000000000000000000)
  k0 := (3677914209701193/1000000000000000000)
  k6 := (579134176005849/50000000000000000)
  q := (167188516352050926381/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13976]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13976]

theorem width_13977 : mW 13977 = 322811410979235 := by
  have hu : mW 13977 ≤ 322811410979235 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13977 ≤ 322811410979234 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13977 : RowArithmetic 13977 (1124539966540028420039/1000000000000000000000000) (609582359634441186106859/1000000000000000000000000) (1836570858617349/250000000000000000000000) where
  r0 := (605172315339/1000000000000000000)
  k0 := (3677716852590293/1000000000000000000)
  k6 := (11582269164722349/1000000000000000000)
  q := (167194497517113283737/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13977]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13977]

theorem width_13978 : mW 13978 = 322892253863016 := by
  have hu : mW 13978 ≤ 322892253863016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13978 ≤ 322892253863015 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13978 : RowArithmetic 13978 (562254177392899061147/500000000000000000000000) (304785475234506857777041/500000000000000000000000) (7344914845023989/1000000000000000000000000) where
  r0 := (302553687279/500000000000000000)
  k0 := (3677519520189023/1000000000000000000)
  k6 := (1447731856724201/125000000000000000)
  q := (167200478468214916769/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13978]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13978]

theorem width_13979 : mW 13979 = 322973111207040 := by
  have hu : mW 13979 ≤ 322973111207040 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13979 ≤ 322973111207039 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13979 : RowArithmetic 13979 (1124476750607809813599/1000000000000000000000000) (24382381717379784216797/40000000000000000000000) (3671773305963139/500000000000000000000000) where
  r0 := (605042445391/1000000000000000000)
  k0 := (919330553123061/250000000000000000)
  k6 := (2895360146830701/250000000000000000)
  q := (167206459205378785511/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13979]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13979]

theorem width_13980 : mW 13980 = 323053983012860 := by
  have hu : mW 13980 ≤ 323053983012860 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13980 ≤ 323053983012859 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13980 : RowArithmetic 13980 (1124445154003686090303/1000000000000000000000000) (38096758564406964641463/62500000000000000000000) (917772341882141/125000000000000000000000) where
  r0 := (302488763917/500000000000000000)
  k0 := (3677124929491777/1000000000000000000)
  k6 := (11581026365301987/1000000000000000000)
  q := (16721243972862784589/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13980]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13980]

theorem width_13981 : mW 13981 = 323134869282028 := by
  have hu : mW 13981 ≤ 323134869282028 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13981 ≤ 323134869282027 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13981 : RowArithmetic 13981 (1124413564971051093709/1000000000000000000000000) (38096045797293237602143/62500000000000000000000) (3670405607148737/500000000000000000000000) where
  r0 := (302456310943/500000000000000000)
  k0 := (3676927671188557/1000000000000000000)
  k6 := (11580612187723209/1000000000000000000)
  q := (167218420037985049729/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13981]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13981]

theorem width_13982 : mW 13982 = 323215770016094 := by
  have hu : mW 13982 ≤ 323215770016094 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13982 ≤ 323215770016093 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13982 : RowArithmetic 13982 (562190991753765549067/500000000000000000000000) (304762665056331770706091/500000000000000000000000) (7339444049528349/1000000000000000000000000) where
  r0 := (604847727543/1000000000000000000)
  k0 := (1838365218787201/500000000000000000)
  k6 := (11580198054578523/1000000000000000000)
  q := (83612200066736672373/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13982]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13982]

theorem width_13983 : mW 13983 = 323296685216611 := by
  have hu : mW 13983 ≤ 323296685216611 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13983 ≤ 323296685216610 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13983 : RowArithmetic 13983 (1124350409610751560241/1000000000000000000000000) (609513929098054568523133/1000000000000000000000000) (7338077240630767/1000000000000000000000000) where
  r0 := (604782844801/1000000000000000000)
  k0 := (459566653580141/125000000000000000)
  k6 := (2315956793171997/200000000000000000)
  q := (41807595003778918639/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13983]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13983]

theorem width_13984 : mW 13984 = 323377614885131 := by
  have hu : mW 13984 ≤ 323377614885131 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13984 ≤ 323377614885130 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13984 : RowArithmetic 13984 (1124318843278339479427/1000000000000000000000000) (304751264856246432851779/500000000000000000000000) (7336710787485813/1000000000000000000000000) where
  r0 := (604717973659/1000000000000000000)
  k0 := (1838168022194833/500000000000000000)
  k6 := (2894842480389913/250000000000000000)
  q := (10452272480183436167/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13984]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13984]

theorem width_13985 : mW 13985 = 323458559023207 := by
  have hu : mW 13985 ≤ 323458559023207 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13985 ≤ 323458559023206 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13985 : RowArithmetic 13985 (1124287284507922217989/1000000000000000000000000) (152372782988901661528571/250000000000000000000000) (7335344689974601/1000000000000000000000000) where
  r0 := (302326557057/500000000000000000)
  k0 := (919034721203717/250000000000000000)
  k6 := (723684745104349/62500000000000000)
  q := (167242339136954192507/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13985]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13985]

theorem width_13986 : mW 13986 = 323539517632389 := by
  have hu : mW 13986 ≤ 323539517632389 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13986 ≤ 323539517632388 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13986 : RowArithmetic 13986 (281063933324282464273/250000000000000000000000) (304739867913512041040451/500000000000000000000000) (183349473699459/25000000000000000000000) where
  r0 := (302294133081/500000000000000000)
  k0 := (1837970874954273/500000000000000000)
  k6 := (5789270983090921/500000000000000000)
  q := (41812079594299061843/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13986]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13986]

theorem width_13987 : mW 13987 = 323620490714231 := by
  have hu : mW 13987 ≤ 323620490714231 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13987 ≤ 323620490714230 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13987 : RowArithmetic 13987 (1124224189643591072661/1000000000000000000000000) (609468341326373615036223/1000000000000000000000000) (3666306780689141/500000000000000000000000) where
  r0 := (3022617149/5000000000000000)
  k0 := (3675744639665547/1000000000000000000)
  k6 := (1157812805508849/100000000000000000)
  q := (83627148701842035241/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13987]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13987]

theorem width_13988 : mW 13988 = 323701478270284 := by
  have hu : mW 13988 ≤ 323701478270284 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13988 ≤ 323701478270283 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13988 : RowArithmetic 13988 (1124192653544937258011/1000000000000000000000000) (609456948453283677294671/1000000000000000000000000) (3665624265027837/500000000000000000000000) where
  r0 := (302229302513/500000000000000000)
  k0 := (3675547554083759/1000000000000000000)
  k6 := (11577714188381593/1000000000000000000)
  q := (20907534527055073119/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13988]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13988]

theorem width_13989 : mW 13989 = 323782480302101 := by
  have hu : mW 13989 ≤ 323782480302101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13989 ≤ 323782480302100 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13989 : RowArithmetic 13989 (1124161124998799579319/1000000000000000000000000) (76180694650922862266771/125000000000000000000000) (7329883853891847/1000000000000000000000000) where
  r0 := (604393791837/1000000000000000000)
  k0 := (3675350493158027/1000000000000000000)
  k6 := (11577300366053219/1000000000000000000)
  q := (836331274077443549/5000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13989]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13989]

theorem width_13990 : mW 13990 = 323863496811234 := by
  have hu : mW 13990 ≤ 323863496811234 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13990 ≤ 323863496811233 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13990 : RowArithmetic 13990 (56206480200140537053/50000000000000000000000) (152358541897075000828037/250000000000000000000000) (7328519532768187/1000000000000000000000000) where
  r0 := (60432899023/100000000000000000)
  k0 := (918788364220799/250000000000000000)
  k6 := (5788443294047719/500000000000000000)
  q := (3345444664017027199/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13990]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13990]

theorem width_13991 : mW 13991 = 323944527799236 := by
  have hu : mW 13991 ≤ 323944527799236 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13991 ≤ 323944527799235 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13991 : RowArithmetic 13991 (281024522638650952283/250000000000000000000000) (609422779595663797557269/1000000000000000000000000) (7327155566566103/1000000000000000000000000) where
  r0 := (604264200201/1000000000000000000)
  k0 := (1837478222625533/500000000000000000)
  k6 := (72352955340627/6250000000000000)
  q := (167278211372551446229/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13991]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13991]

theorem width_13992 : mW 13992 = 324025573267659 := by
  have hu : mW 13992 ≤ 324025573267659 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13992 ≤ 324025573267658 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13992 : RowArithmetic 13992 (562033292325906693129/500000000000000000000000) (152352848307275824815321/250000000000000000000000) (7325791955167079/1000000000000000000000000) where
  r0 := (604199421749/1000000000000000000)
  k0 := (3674759458262561/1000000000000000000)
  k6 := (11576059165259939/1000000000000000000)
  q := (41821047332652968843/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13992]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13992]

theorem width_13993 : mW 13993 = 324106633218055 := by
  have hu : mW 13993 ≤ 324106633218055 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13993 ≤ 324106633218054 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13993 : RowArithmetic 13993 (1124035086292075023177/1000000000000000000000000) (76175001061030937512099/125000000000000000000000) (7324428698452649/1000000000000000000000000) where
  r0 := (60413465487/100000000000000000)
  k0 := (91864062397737/25000000000000000)
  k6 := (11575645520366371/1000000000000000000)
  q := (167290167075055550021/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13993]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13993]

theorem width_13994 : mW 13994 = 324187707651977 := by
  have hu : mW 13994 ≤ 324187707651977 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13994 ≤ 324187707651976 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13994 : RowArithmetic 13994 (562001797736512315657/500000000000000000000000) (121877725074545126058997/200000000000000000000000) (1830766449076093/250000000000000000000000) where
  r0 := (604069899561/1000000000000000000)
  k0 := (1837182779093329/500000000000000000)
  k6 := (11575231919811693/1000000000000000000)
  q := (6691845784236214749/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13994]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13994]

theorem width_13995 : mW 13995 = 324268796570978 := by
  have hu : mW 13995 ≤ 324268796570978 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13995 ≤ 324268796570977 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13995 : RowArithmetic 13995 (140496514024037383763/125000000000000000000000) (609377243882166982206657/1000000000000000000000000) (7321703248603857/1000000000000000000000000) where
  r0 := (604005155819/1000000000000000000)
  k0 := (1837084322544467/500000000000000000)
  k6 := (11574818363587983/1000000000000000000)
  q := (167302121923184225943/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13995]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13995]

theorem width_13996 : mW 13996 = 324349899976610 := by
  have hu : mW 13996 ≤ 324349899976610 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13996 ≤ 324349899976609 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13996 : RowArithmetic 13996 (112394063644753673287/100000000000000000000000) (609365864016200996341939/1000000000000000000000000) (7320341055232787/1000000000000000000000000) where
  r0 := (301970211821/500000000000000000)
  k0 := (3673971756614183/1000000000000000000)
  k6 := (462976194067493/40000000000000000)
  q := (41827024756728753011/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13996]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13996]

theorem width_13997 : mW 13997 = 324431017870426 := by
  have hu : mW 13997 ≤ 324431017870426 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13997 ≤ 324431017870425 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13997 : RowArithmetic 13997 (561954584118188186437/500000000000000000000000) (121870897154891429390413/200000000000000000000000) (1829744804018217/250000000000000000000000) where
  r0 := (603875703027/1000000000000000000)
  k0 := (1836887446378619/500000000000000000)
  k6 := (57869956920509/5000000000000000)
  q := (167314075917120613311/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13997]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13997]

theorem width_13998 : mW 13998 = 324512150253980 := by
  have hu : mW 13998 ≤ 324512150253980 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13998 ≤ 324512150253979 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13998 : RowArithmetic 13998 (280969426889114276013/250000000000000000000000) (152335777289141279423311/250000000000000000000000) (3658808865502919/500000000000000000000000) where
  r0 := (60381099397/100000000000000000)
  k0 := (3673578053509889/1000000000000000000)
  k6 := (2314715592164699/200000000000000000)
  q := (33464010518764782387/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13998]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13998]

theorem width_13999 : mW 13999 = 324593297128822 := by
  have hu : mW 13999 ≤ 324593297128822 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13999 ≤ 324593297128821 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13999 : RowArithmetic 13999 (561923127202710664939/500000000000000000000000) (121866346832430930674493/200000000000000000000000) (7316256599913569/1000000000000000000000000) where
  r0 := (603746296469/1000000000000000000)
  k0 := (459172654858751/125000000000000000)
  k6 := (11573164581844497/1000000000000000000)
  q := (167326029057047786023/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13999]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13999]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13925 then ⟨(281548569271995555697/250000000000000000000000), (610177892906420748115821/1000000000000000000000000), (7417944103759921/1000000000000000000000000)⟩ else
  if n = 13926 then ⟨(1126162268071127789541/1000000000000000000000000), (30508319920881161854583/50000000000000000000000), (7416556818890647/1000000000000000000000000)⟩ else
  if n = 13927 then ⟨(1126130266755382563207/1000000000000000000000000), (305077452789631505975677/500000000000000000000000), (7415169896630237/1000000000000000000000000)⟩ else
  if n = 13928 then ⟨(56304913656916035501/50000000000000000000000), (305071707195480750337811/500000000000000000000000), (1853445834214249/250000000000000000000000)⟩ else
  if n = 13929 then ⟨(1126066287217517977227/1000000000000000000000000), (610131924852340205896837/1000000000000000000000000), (7412397139449307/1000000000000000000000000)⟩ else
  if n = 13930 then ⟨(563017154495275845657/500000000000000000000000), (122024087392604171693849/200000000000000000000000), (11857618086857/1600000000000000000000)⟩ else
  if n = 13931 then ⟨(140750292306874943909/125000000000000000000000), (610108950722625173783421/1000000000000000000000000), (7409625831244433/1000000000000000000000000)⟩ else
  if n = 13932 then ⟨(22519407512168792587/20000000000000000000000), (122019493226155019502199/200000000000000000000000), (3704120360102121/500000000000000000000000)⟩ else
  if n = 13933 then ⟨(140742302556056446971/125000000000000000000000), (610085983187092682955483/1000000000000000000000000), (3703427985521819/500000000000000000000000)⟩ else
  if n = 13934 then ⟨(56295323648630800761/50000000000000000000000), (122014900378240000827961/200000000000000000000000), (3702735791820629/500000000000000000000000)⟩ else
  if n = 13935 then ⟨(17591789580914289787/15625000000000000000000), (610063022242719311107959/1000000000000000000000000), (1851021889468947/250000000000000000000000)⟩ else
  if n = 13936 then ⟨(1125842601063729140113/1000000000000000000000000), (6100515442412730651181/10000000000000000000000), (7402703893625943/1000000000000000000000000)⟩ else
  if n = 13937 then ⟨(1125810676625843943263/1000000000000000000000000), (610040067886483749363961/1000000000000000000000000), (7401320590770537/1000000000000000000000000)⟩ else
  if n = 13938 then ⟨(1125778759862441671181/1000000000000000000000000), (305014296588986962473067/500000000000000000000000), (7399937649188339/1000000000000000000000000)⟩ else
  if n = 13939 then ⟨(1125746850771109016549/1000000000000000000000000), (61001712011536633679219/100000000000000000000000), (462409691797393/62500000000000000000000)⟩ else
  if n = 13940 then ⟨(225142989869886368163/200000000000000000000000), (610005648698283890042157/1000000000000000000000000), (7397172849359301/1000000000000000000000000)⟩ else
  if n = 13941 then ⟨(1125683055594996377397/1000000000000000000000000), (609994178926349497470597/1000000000000000000000000), (3697895495435163/500000000000000000000000)⟩ else
  if n = 13942 then ⟨(1125651169505391031587/1000000000000000000000000), (304991355399593150966939/500000000000000000000000), (1848602373292601/250000000000000000000000)⟩ else
  if n = 13943 then ⟨(562809645539102589301/500000000000000000000000), (152492811079104367922819/250000000000000000000000), (924128544517329/125000000000000000000000)⟩ else
  if n = 13944 then ⟨(140698427538878570483/125000000000000000000000), (152489944869416589235787/250000000000000000000000), (739164757965413/100000000000000000000000)⟩ else
  if n = 13945 then ⟨(562777778600725651873/500000000000000000000000), (76243539535319548783221/125000000000000000000000), (461891697724753/62500000000000000000000)⟩ else
  if n = 13946 then ⟨(281380925436766570297/250000000000000000000000), (304968427365355567913249/500000000000000000000000), (923610888480457/125000000000000000000000)⟩ else
  if n = 13947 then ⟨(70343240871591559511/62500000000000000000000), (15248134870543857353087/25000000000000000000000), (7387507412276181/1000000000000000000000000)⟩ else
  if n = 13948 then ⟨(112546001379424213597/100000000000000000000000), (304956968277654824501151/500000000000000000000000), (3693064038386497/500000000000000000000000)⟩ else
  if n = 13949 then ⟨(1125428181290991225867/1000000000000000000000000), (609902479931001114812069/1000000000000000000000000), (461546818825839/62500000000000000000000)⟩ else
  if n = 13950 then ⟨(1125396356433308975439/1000000000000000000000000), (609891024948452728823467/1000000000000000000000000), (7383370485476943/1000000000000000000000000)⟩ else
  if n = 13951 then ⟨(281341134804697678321/250000000000000000000000), (609879571607288688306367/1000000000000000000000000), (7381992229442981/1000000000000000000000000)⟩ else
  if n = 13952 then ⟨(281333182411258482709/250000000000000000000000), (609868119907133214429873/1000000000000000000000000), (1476122866598213/200000000000000000000000)⟩ else
  if n = 13953 then ⟨(1125300927709637682391/1000000000000000000000000), (609856669847610698718793/1000000000000000000000000), (1844809199000199/250000000000000000000000)⟩ else
  if n = 13954 then ⟨(562634566705100396603/500000000000000000000000), (609845221428345661468941/1000000000000000000000000), (3688929809175889/500000000000000000000000)⟩ else
  if n = 13955 then ⟨(45009493869772922177/40000000000000000000000), (304916887324481364891649/500000000000000000000000), (1844120699980917/250000000000000000000000)⟩ else
  if n = 13956 then ⟨(1125205567709605818807/1000000000000000000000000), (121964465901817331602481/200000000000000000000000), (7375106340596193/1000000000000000000000000)⟩ else
  if n = 13957 then ⟨(1125173796303651402997/1000000000000000000000000), (609810886008342302820599/1000000000000000000000000), (3686865120124567/500000000000000000000000)⟩ else
  if n = 13958 then ⟨(70321377032753905707/62500000000000000000000), (121959888829270923415349/200000000000000000000000), (7372354498762297/1000000000000000000000000)⟩ else
  if n = 13959 then ⟨(562555138184221365977/500000000000000000000000), (609788003922748688415001/1000000000000000000000000), (3685489558007769/500000000000000000000000)⟩ else
  if n = 13960 then ⟨(1125078527834396736511/1000000000000000000000000), (609776565337149806878861/1000000000000000000000000), (7369604091888767/1000000000000000000000000)⟩ else
  if n = 13961 then ⟨(281261696729882817353/250000000000000000000000), (609765128389183255535999/1000000000000000000000000), (1473645885252397/200000000000000000000000)⟩ else
  if n = 13962 then ⟨(562507526810726135649/500000000000000000000000), (121950738615694899246191/200000000000000000000000), (368342755950759/50000000000000000000000)⟩ else
  if n = 13963 then ⟨(112498332793776724017/100000000000000000000000), (609742259404649061987939/1000000000000000000000000), (920685146253551/125000000000000000000000)⟩ else
  if n = 13964 then ⟨(22499032197321704593/20000000000000000000000), (304865413683666334512303/500000000000000000000000), (7364107579181801/1000000000000000000000000)⟩ else
  if n = 13965 then ⟨(1124919899404015065287/1000000000000000000000000), (304859698483075545824769/500000000000000000000000), (920341793294437/125000000000000000000000)⟩ else
  if n = 13966 then ⟨(1124888196549167721487/1000000000000000000000000), (609707968200730276632737/1000000000000000000000000), (294454458857189/40000000000000000000000)⟩ else
  if n = 13967 then ⟨(562428250649576972289/500000000000000000000000), (609696541070696271680397/1000000000000000000000000), (7359988954284723/1000000000000000000000000)⟩ else
  if n = 13968 then ⟨(562412406825793313877/500000000000000000000000), (762106394469593993919/1250000000000000000000), (919827099350103/125000000000000000000000)⟩ else
  if n = 13969 then ⟨(112479313360407843613/100000000000000000000000), (304836845857646674368127/500000000000000000000000), (1839311248214591/250000000000000000000000)⟩ else
  if n = 13970 then ⟨(1124761461154242994209/1000000000000000000000000), (304831134744588543881213/500000000000000000000000), (735587354833773/100000000000000000000000)⟩ else
  if n = 13971 then ⟨(281182449074924165721/250000000000000000000000), (609650848896952921907599/1000000000000000000000000), (7354502461119427/1000000000000000000000000)⟩ else
  if n = 13972 then ⟨(562349069519027194733/500000000000000000000000), (304819714969123741239589/500000000000000000000000), (7353131731083921/1000000000000000000000000)⟩ else
  if n = 13973 then ⟨(224933297873386534431/200000000000000000000000), (76203501576585939684639/125000000000000000000000), (3675880679055873/500000000000000000000000)⟩ else
  if n = 13974 then ⟨(1124634847283950741831/1000000000000000000000000), (76202074614987485834379/125000000000000000000000), (7350391342083561/1000000000000000000000000)⟩ else
  if n = 13975 then ⟨(562301606393362912877/500000000000000000000000), (76200647857438944051289/125000000000000000000000), (1469804336575991/200000000000000000000000)⟩ else
  if n = 13976 then ⟨(281142896468219618657/250000000000000000000000), (304796885215574773679401/500000000000000000000000), (3673826190190831/500000000000000000000000)⟩ else
  if n = 13977 then ⟨(1124539966540028420039/1000000000000000000000000), (609582359634441186106859/1000000000000000000000000), (1836570858617349/250000000000000000000000)⟩ else
  if n = 13978 then ⟨(562254177392899061147/500000000000000000000000), (304785475234506857777041/500000000000000000000000), (7344914845023989/1000000000000000000000000)⟩ else
  if n = 13979 then ⟨(1124476750607809813599/1000000000000000000000000), (24382381717379784216797/40000000000000000000000), (3671773305963139/500000000000000000000000)⟩ else
  if n = 13980 then ⟨(1124445154003686090303/1000000000000000000000000), (38096758564406964641463/62500000000000000000000), (917772341882141/125000000000000000000000)⟩ else
  if n = 13981 then ⟨(1124413564971051093709/1000000000000000000000000), (38096045797293237602143/62500000000000000000000), (3670405607148737/500000000000000000000000)⟩ else
  if n = 13982 then ⟨(562190991753765549067/500000000000000000000000), (304762665056331770706091/500000000000000000000000), (7339444049528349/1000000000000000000000000)⟩ else
  if n = 13983 then ⟨(1124350409610751560241/1000000000000000000000000), (609513929098054568523133/1000000000000000000000000), (7338077240630767/1000000000000000000000000)⟩ else
  if n = 13984 then ⟨(1124318843278339479427/1000000000000000000000000), (304751264856246432851779/500000000000000000000000), (7336710787485813/1000000000000000000000000)⟩ else
  if n = 13985 then ⟨(1124287284507922217989/1000000000000000000000000), (152372782988901661528571/250000000000000000000000), (7335344689974601/1000000000000000000000000)⟩ else
  if n = 13986 then ⟨(281063933324282464273/250000000000000000000000), (304739867913512041040451/500000000000000000000000), (183349473699459/25000000000000000000000)⟩ else
  if n = 13987 then ⟨(1124224189643591072661/1000000000000000000000000), (609468341326373615036223/1000000000000000000000000), (3666306780689141/500000000000000000000000)⟩ else
  if n = 13988 then ⟨(1124192653544937258011/1000000000000000000000000), (609456948453283677294671/1000000000000000000000000), (3665624265027837/500000000000000000000000)⟩ else
  if n = 13989 then ⟨(1124161124998799579319/1000000000000000000000000), (76180694650922862266771/125000000000000000000000), (7329883853891847/1000000000000000000000000)⟩ else
  if n = 13990 then ⟨(56206480200140537053/50000000000000000000000), (152358541897075000828037/250000000000000000000000), (7328519532768187/1000000000000000000000000)⟩ else
  if n = 13991 then ⟨(281024522638650952283/250000000000000000000000), (609422779595663797557269/1000000000000000000000000), (7327155566566103/1000000000000000000000000)⟩ else
  if n = 13992 then ⟨(562033292325906693129/500000000000000000000000), (152352848307275824815321/250000000000000000000000), (7325791955167079/1000000000000000000000000)⟩ else
  if n = 13993 then ⟨(1124035086292075023177/1000000000000000000000000), (76175001061030937512099/125000000000000000000000), (7324428698452649/1000000000000000000000000)⟩ else
  if n = 13994 then ⟨(562001797736512315657/500000000000000000000000), (121877725074545126058997/200000000000000000000000), (1830766449076093/250000000000000000000000)⟩ else
  if n = 13995 then ⟨(140496514024037383763/125000000000000000000000), (609377243882166982206657/1000000000000000000000000), (7321703248603857/1000000000000000000000000)⟩ else
  if n = 13996 then ⟨(112394063644753673287/100000000000000000000000), (609365864016200996341939/1000000000000000000000000), (7320341055232787/1000000000000000000000000)⟩ else
  if n = 13997 then ⟨(561954584118188186437/500000000000000000000000), (121870897154891429390413/200000000000000000000000), (1829744804018217/250000000000000000000000)⟩ else
  if n = 13998 then ⟨(280969426889114276013/250000000000000000000000), (152335777289141279423311/250000000000000000000000), (3658808865502919/500000000000000000000000)⟩ else
  ⟨(561923127202710664939/500000000000000000000000), (121866346832430930674493/200000000000000000000000), (7316256599913569/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13925 ≤ n) (hb : n ≤ 13999) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13925
  · exact row_13926
  · exact row_13927
  · exact row_13928
  · exact row_13929
  · exact row_13930
  · exact row_13931
  · exact row_13932
  · exact row_13933
  · exact row_13934
  · exact row_13935
  · exact row_13936
  · exact row_13937
  · exact row_13938
  · exact row_13939
  · exact row_13940
  · exact row_13941
  · exact row_13942
  · exact row_13943
  · exact row_13944
  · exact row_13945
  · exact row_13946
  · exact row_13947
  · exact row_13948
  · exact row_13949
  · exact row_13950
  · exact row_13951
  · exact row_13952
  · exact row_13953
  · exact row_13954
  · exact row_13955
  · exact row_13956
  · exact row_13957
  · exact row_13958
  · exact row_13959
  · exact row_13960
  · exact row_13961
  · exact row_13962
  · exact row_13963
  · exact row_13964
  · exact row_13965
  · exact row_13966
  · exact row_13967
  · exact row_13968
  · exact row_13969
  · exact row_13970
  · exact row_13971
  · exact row_13972
  · exact row_13973
  · exact row_13974
  · exact row_13975
  · exact row_13976
  · exact row_13977
  · exact row_13978
  · exact row_13979
  · exact row_13980
  · exact row_13981
  · exact row_13982
  · exact row_13983
  · exact row_13984
  · exact row_13985
  · exact row_13986
  · exact row_13987
  · exact row_13988
  · exact row_13989
  · exact row_13990
  · exact row_13991
  · exact row_13992
  · exact row_13993
  · exact row_13994
  · exact row_13995
  · exact row_13996
  · exact row_13997
  · exact row_13998
  · exact row_13999

end BstLean.Part271.R3.Rows13925
