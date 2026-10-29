import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14717–14791. -/
namespace BstLean.Part271.R3.Rows14717
open Real BstLean.Part130 BstLean.Part227

theorem width_14717 : mW 14717 = 386694072140391 := by
  have hu : mW 14717 ≤ 386694072140391 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14717 ≤ 386694072140390 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14717 : RowArithmetic 14717 (220613932432029238103/200000000000000000000000) (150390457518071315608247/250000000000000000000000) (1284702788052461/200000000000000000000000) where
  r0 := (560107083621/1000000000000000000)
  k0 := (3538134157847799/1000000000000000000)
  k6 := (2257464797650597/200000000000000000)
  q := (171563399360119931147/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14717]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14717]

theorem width_14718 : mW 14718 = 386786043616301 := by
  have hu : mW 14718 ≤ 386786043616301 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14718 ≤ 386786043616300 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14718 : RowArithmetic 14718 (1103043064037177127031/1000000000000000000000000) (300775766625213596062299/500000000000000000000000) (1284475896127431/200000000000000000000000) where
  r0 := (280025000353/500000000000000000)
  k0 := (3537953860041013/1000000000000000000)
  k6 := (5643470264344571/500000000000000000)
  q := (171569228010153382517/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14718]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14718]

theorem width_14719 : mW 14719 = 386878030715817 := by
  have hu : mW 14719 ≤ 386878030715817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14719 ≤ 386878030715816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14719 : RowArithmetic 14719 (1103016471957533981409/1000000000000000000000000) (601541237812898563268073/1000000000000000000000000) (1284249060215747/200000000000000000000000) where
  r0 := (111998585497/200000000000000000)
  k0 := (884443395916669/250000000000000000)
  k6 := (564327855410199/50000000000000000)
  q := (3431501129243585139/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14719]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14719]

theorem width_14720 : mW 14720 = 386970033440530 := by
  have hu : mW 14720 ≤ 386970033440530 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14720 ≤ 386970033440529 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14720 : RowArithmetic 14720 (1102989885919419741003/1000000000000000000000000) (601530943759401898987151/1000000000000000000000000) (6420111401498299/1000000000000000000000000) where
  r0 := (279967931979/500000000000000000)
  k0 := (1727340492543/488281250000000)
  k6 := (11286173726790863/1000000000000000000)
  q := (85790442358108866439/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14720]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14720]

theorem width_14721 : mW 14721 = 387062051792033 := by
  have hu : mW 14721 ≤ 387062051792033 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14721 ≤ 387062051792032 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14721 : RowArithmetic 14721 (551481652960518601273/500000000000000000000000) (75190081386204981750703/125000000000000000000000) (3134266495023/488281250000000000000) where
  r0 := (559878810121/1000000000000000000)
  k0 := (1768706547607909/500000000000000000)
  k6 := (2257158076888631/200000000000000000)
  q := (85793356386144492651/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14721]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14721]

theorem width_14722 : mW 14722 = 387154085771918 := by
  have hu : mW 14722 ≤ 387154085771918 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14722 ≤ 387154085771917 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14722 : RowArithmetic 14722 (551468365980295141893/500000000000000000000000) (300755179901657598144781/500000000000000000000000) (6417844441916459/1000000000000000000000000) where
  r0 := (139955441493/250000000000000000)
  k0 := (707446576625379/200000000000000000)
  k6 := (5642703540577111/500000000000000000)
  q := (171592540630413185803/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14722]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14722]

theorem width_14723 : mW 14723 = 387246135381777 := by
  have hu : mW 14723 ≤ 387246135381777 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14723 ≤ 387246135381776 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14723 : RowArithmetic 14723 (1102910164036283585713/1000000000000000000000000) (601500069900130714372767/1000000000000000000000000) (1283342276347541/200000000000000000000000) where
  r0 := (55976473151/100000000000000000)
  k0 := (3537052692461409/1000000000000000000)
  k6 := (1410627977114679/125000000000000000)
  q := (17159836829061050253/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14723]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14723]

theorem width_14724 : mW 14724 = 387338200623204 := by
  have hu : mW 14724 ≤ 387338200623204 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14724 ≤ 387338200623203 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14724 : RowArithmetic 14724 (1102883602146321519417/1000000000000000000000000) (30074489068989464853431/50000000000000000000000) (6415578601182189/1000000000000000000000000) where
  r0 := (559707706731/1000000000000000000)
  k0 := (3536872523209997/1000000000000000000)
  k6 := (11284640591726153/1000000000000000000)
  q := (171604195752901100213/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14724]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14724]

theorem width_14725 : mW 14725 = 387430281497791 := by
  have hu : mW 14725 ≤ 387430281497791 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14725 ≤ 387430281497790 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14725 : RowArithmetic 14725 (1102857046288910052397/1000000000000000000000000) (120295898848398800577049/200000000000000000000000) (256577844006453/40000000000000000000000) where
  r0 := (279825345817/500000000000000000)
  k0 := (884173093843193/250000000000000000)
  k6 := (5642128702786879/500000000000000000)
  q := (34322004603461028031/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14725]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14725]

theorem width_14726 : mW 14726 = 387522378007130 := by
  have hu : mW 14726 ≤ 387522378007130 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14726 ≤ 387522378007129 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14726 : RowArithmetic 14726 (1102830496462255834389/1000000000000000000000000) (300734604243223938305159/500000000000000000000000) (20041605870583/3125000000000000000000) where
  r0 := (69949210777/125000000000000000)
  k0 := (3536512248943527/1000000000000000000)
  k6 := (11283874258453617/1000000000000000000)
  q := (42903962520960695059/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14726]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14726]

theorem width_14727 : mW 14727 = 387614490152814 := by
  have hu : mW 14727 ≤ 387614490152814 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14727 ≤ 387614490152813 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14727 : RowArithmetic 14727 (1102803952664565761137/1000000000000000000000000) (300729462056427038415837/500000000000000000000000) (3206090968184681/500000000000000000000000) where
  r0 := (22381467619/40000000000000000)
  k0 := (884083035979803/250000000000000000)
  k6 := (2256698230071821/200000000000000000)
  q := (42905419238133543729/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14727]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14727]

theorem width_14728 : mW 14728 = 387706617936436 := by
  have hu : mW 14728 ≤ 387706617936436 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14728 ≤ 387706617936435 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14728 : RowArithmetic 14728 (1102777414894047410643/1000000000000000000000000) (601448641120915891409517/1000000000000000000000000) (6411050273421233/1000000000000000000000000) where
  r0 := (69934963051/125000000000000000)
  k0 := (3536152060293619/1000000000000000000)
  k6 := (11283108081283597/1000000000000000000)
  q := (171627503623399475233/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14728]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14728]

theorem width_14729 : mW 14729 = 387798761359588 := by
  have hu : mW 14729 ≤ 387798761359588 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14729 ≤ 387798761359587 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14729 : RowArithmetic 14729 (1102750883148909478363/1000000000000000000000000) (601438359510336679243149/1000000000000000000000000) (6409918889653729/1000000000000000000000000) where
  r0 := (279711364007/500000000000000000)
  k0 := (707194399613371/200000000000000000)
  k6 := (11282725051220471/1000000000000000000)
  q := (171633330096458828803/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14729]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14729]

theorem width_14730 : mW 14730 = 387890920423864 := by
  have hu : mW 14730 ≤ 387890920423864 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14730 ≤ 387890920423863 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14730 : RowArithmetic 14730 (1102724357427360469911/1000000000000000000000000) (601428079280819848886093/1000000000000000000000000) (1602196946244601/250000000000000000000000) where
  r0 := (55936576129/100000000000000000)
  k0 := (883947989308177/250000000000000000)
  k6 := (5641171030081553/500000000000000000)
  q := (6865566254869295193/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14730]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14730]

theorem width_14731 : mW 14731 = 387983095130857 := by
  have hu : mW 14731 ≤ 387983095130857 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14731 ≤ 387983095130856 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14731 : RowArithmetic 14731 (34459307428987812751/31250000000000000000000) (300708900216034459802241/500000000000000000000000) (6407656959306867/1000000000000000000000000) where
  r0 := (559308804233/1000000000000000000)
  k0 := (707122387556993/200000000000000000)
  k6 := (141024488851311/12500000000000000)
  q := (42911245612310067269/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14731]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14731]

theorem width_14732 : mW 14732 = 388075285482159 := by
  have hu : mW 14732 ≤ 388075285482159 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14732 ≤ 388075285482158 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14732 : RowArithmetic 14732 (110267132404786883141/100000000000000000000000) (601407522963787501736593/1000000000000000000000000) (3203263206275389/500000000000000000000000) where
  r0 := (279625928421/500000000000000000)
  k0 := (3535431939723731/1000000000000000000)
  k6 := (11281576195039177/1000000000000000000)
  q := (171650808329002633917/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14732]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14732]

theorem width_14733 : mW 14733 = 388167491479363 := by
  have hu : mW 14733 ≤ 388167491479363 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14733 ≤ 388167491479362 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14733 : RowArithmetic 14733 (220528963277269584753/200000000000000000000000) (601397246875679295489239/1000000000000000000000000) (1601349036155453/250000000000000000000000) where
  r0 := (559194919113/1000000000000000000)
  k0 := (3535251963039629/1000000000000000000)
  k6 := (11281193320959379/1000000000000000000)
  q := (42914158502759902073/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14733]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14733]

theorem width_14734 : mW 14734 = 388259713124063 := by
  have hu : mW 14734 ≤ 388259713124063 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14734 ≤ 388259713124062 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14734 : RowArithmetic 14734 (55130915737062925719/50000000000000000000000) (300693486083724047607361/500000000000000000000000) (6404266155431669/1000000000000000000000000) where
  r0 := (279568995523/500000000000000000)
  k0 := (141402880309437/40000000000000000)
  k6 := (11280810485858871/1000000000000000000)
  q := (171662459495371322727/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14734]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14734]

theorem width_14735 : mW 14735 = 388351950417852 := by
  have hu : mW 14735 ≤ 388351950417852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14735 ≤ 388351950417851 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14735 : RowArithmetic 14735 (1102591819110812947641/1000000000000000000000000) (300688349419398889615993/500000000000000000000000) (3201568222446047/500000000000000000000000) where
  r0 := (559081072637/1000000000000000000)
  k0 := (1767446036901619/500000000000000000)
  k6 := (70502673060819/6250000000000000)
  q := (85834142391008952167/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14735]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14735]

theorem width_14736 : mW 14736 = 388444203362323 := by
  have hu : mW 14736 ≤ 388444203362323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14736 ≤ 388444203362322 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14736 : RowArithmetic 14736 (1102565329493224247513/1000000000000000000000000) (601366426889432281380663/1000000000000000000000000) (6402007012914871/1000000000000000000000000) where
  r0 := (139756040971/250000000000000000)
  k0 := (883678040309627/250000000000000000)
  k6 := (451201797302771/40000000000000000)
  q := (17167410987099947681/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14736]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14736]

theorem width_14737 : mW 14737 = 388536471959068 := by
  have hu : mW 14737 ≤ 388536471959068 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14737 ≤ 388536471959067 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14737 : RowArithmetic 14737 (137817355735838318921/125000000000000000000000) (601356156319055637288437/1000000000000000000000000) (1280175571882367/200000000000000000000000) where
  r0 := (111793452957/200000000000000000)
  k0 := (883633067509669/250000000000000000)
  k6 := (11279662214366963/1000000000000000000)
  q := (42919983690584040109/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14737]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14737]

theorem width_14738 : mW 14738 = 388628756209682 := by
  have hu : mW 14738 ≤ 388628756209682 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14738 ≤ 388628756209681 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14738 : RowArithmetic 14738 (1102512368289473372813/1000000000000000000000000) (30067294356368600526939/50000000000000000000000) (1279949796858961/200000000000000000000000) where
  r0 := (279455187669/500000000000000000)
  k0 := (3534352400200679/1000000000000000000)
  k6 := (5639639767558749/500000000000000000)
  q := (171685759456048072083/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14738]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14738]

theorem width_14739 : mW 14739 = 388721056115758 := by
  have hu : mW 14739 ≤ 388721056115758 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14739 ≤ 388721056115757 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14739 : RowArithmetic 14739 (137810737087467471631/125000000000000000000000) (601335619314085613092551/1000000000000000000000000) (639862038747567/100000000000000000000000) where
  r0 := (27942674777/50000000000000000)
  k0 := (706834510343659/200000000000000000)
  k6 := (176232763981473/15625000000000000)
  q := (21461447994019415651/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14739]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14739]

theorem width_14740 : mW 14740 = 388813371678889 := by
  have hu : mW 14740 ≤ 388813371678889 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14740 ≤ 388813371678888 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14740 : RowArithmetic 14740 (1102459431115721491517/1000000000000000000000000) (601325352878900745140913/1000000000000000000000000) (6397492068866351/1000000000000000000000000) where
  r0 := (558796625389/1000000000000000000)
  k0 := (1766996362294229/500000000000000000)
  k6 := (5639257146725339/500000000000000000)
  q := (34339481650135605971/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14740]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14740]

theorem width_14741 : mW 14741 = 388905702900669 := by
  have hu : mW 14741 ≤ 388905702900669 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14741 ≤ 388905702900668 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14741 : RowArithmetic 14741 (137804121441954314011/125000000000000000000000) (120263017564304357546273/200000000000000000000000) (639636402837879/100000000000000000000000) where
  r0 := (558739764883/1000000000000000000)
  k0 := (441726614851013/125000000000000000)
  k6 := (11278131731020113/1000000000000000000)
  q := (8585161617581814633/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14741]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14741]

theorem width_14742 : mW 14742 = 388998049782691 := by
  have hu : mW 14742 ≤ 388998049782691 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14742 ≤ 388998049782690 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14742 : RowArithmetic 14742 (1102406517957695930199/1000000000000000000000000) (120260964828330655578327/200000000000000000000000) (319761813296249/50000000000000000000000) where
  r0 := (558682914019/1000000000000000000)
  k0 := (706726626874201/200000000000000000)
  k6 := (451109968300639/40000000000000000)
  q := (10731816015940638553/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14742]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14742]

theorem width_14743 : mW 14743 = 389090412326548 := by
  have hu : mW 14743 ≤ 389090412326548 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14743 ≤ 389090412326547 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14743 : RowArithmetic 14743 (1102380070380123518533/1000000000000000000000000) (601294561838999737591981/1000000000000000000000000) (1598527195354237/250000000000000000000000) where
  r0 := (111725214559/200000000000000000)
  k0 := (3533453371274093/1000000000000000000)
  k6 := (5638683361465831/500000000000000000)
  q := (85857439980469951117/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14743]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14743]

theorem width_14744 : mW 14744 = 389182790533835 := by
  have hu : mW 14744 ≤ 389182790533835 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14744 ≤ 389182790533834 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14744 : RowArithmetic 14744 (1102353628801134860743/1000000000000000000000000) (601284300913265819615147/1000000000000000000000000) (6392981574766723/1000000000000000000000000) where
  r0 := (558569241209/1000000000000000000)
  k0 := (35332736295143/10000000000000000)
  k6 := (451079371090423/40000000000000000)
  q := (85860351734662722613/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14744]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14744]

theorem width_14745 : mW 14745 = 389275184406144 := by
  have hu : mW 14745 ≤ 389275184406144 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14745 ≤ 389275184406143 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14745 : RowArithmetic 14745 (551163596609474758411/500000000000000000000000) (30063702068207813400353/50000000000000000000000) (319592732294321/50000000000000000000000) where
  r0 := (558512419259/1000000000000000000)
  k0 := (883273477272139/250000000000000000)
  k6 := (2819150467624029/250000000000000000)
  q := (171726526780226938823/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14745]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14745]

theorem width_14746 : mW 14746 = 389367593945071 := by
  have hu : mW 14746 ≤ 389367593945071 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14746 ≤ 389367593945070 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14746 : RowArithmetic 14746 (137787595453973248977/125000000000000000000000) (75157972898921987893861/125000000000000000000000) (159768199867203/25000000000000000000000) where
  r0 := (279227803471/500000000000000000)
  k0 := (883228552497657/250000000000000000)
  k6 := (1127621950263169/100000000000000000)
  q := (171732349893664472619/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14746]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14746]

theorem width_14747 : mW 14747 = 389460019152208 := by
  have hu : mW 14747 ≤ 389460019152208 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14747 ≤ 389460019152207 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14747 : RowArithmetic 14747 (1102274340037865198561/1000000000000000000000000) (30062676319731484249381/50000000000000000000000) (798700202635501/125000000000000000000000) where
  r0 := (17449962633/31250000000000000)
  k0 := (883183633054361/250000000000000000)
  k6 := (11275837173660701/1000000000000000000)
  q := (85869086404829066401/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14747]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14747]

theorem width_14748 : mW 14748 = 389552460029149 := by
  have hu : mW 14748 ≤ 389552460029149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14748 ≤ 389552460029148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14748 : RowArithmetic 14748 (551123961217703930109/500000000000000000000000) (601243270973622592351581/1000000000000000000000000) (6388475524986267/1000000000000000000000000) where
  r0 := (558342011199/1000000000000000000)
  k0 := (3532554875765931/1000000000000000000)
  k6 := (2255090976715311/200000000000000000)
  q := (171743995528228002153/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14748]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14748]

theorem width_14749 : mW 14749 = 389644916577488 := by
  have hu : mW 14749 ≤ 389644916577488 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14749 ≤ 389644916577487 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14749 : RowArithmetic 14749 (1102221510822635375881/1000000000000000000000000) (601233016928059643519689/1000000000000000000000000) (6387349706307119/1000000000000000000000000) where
  r0 := (69785653471/125000000000000000)
  k0 := (883093810157463/250000000000000000)
  k6 := (11275072632372663/1000000000000000000)
  q := (3434996360987883201/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14749]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14749]

theorem width_14750 : mW 14750 = 389737388798820 := by
  have hu : mW 14750 ≤ 389737388798820 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14750 ≤ 389737388798819 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14750 : RowArithmetic 14750 (1102195105197769388303/1000000000000000000000000) (601222764257646124741983/1000000000000000000000000) (6386224164958801/1000000000000000000000000) where
  r0 := (279114226981/500000000000000000)
  k0 := (1766097813404647/500000000000000000)
  k6 := (11274690420042433/1000000000000000000)
  q := (171755640373176682469/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14750]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14750]

theorem width_14751 : mW 14751 = 389829876694738 := by
  have hu : mW 14751 ≤ 389829876694738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14751 ≤ 389829876694737 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14751 : RowArithmetic 14751 (1102168705559033079733/1000000000000000000000000) (601212512962087253982581/1000000000000000000000000) (319254945042681/50000000000000000000000) where
  r0 := (558171689777/1000000000000000000)
  k0 := (706403206858971/200000000000000000)
  k6 := (5637154123289639/500000000000000000)
  q := (8588073124979782099/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14751]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14751]

theorem width_14752 : mW 14752 = 389922380266836 := by
  have hu : mW 14752 ≤ 389922380266836 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14752 ≤ 389922380266835 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14752 : RowArithmetic 14752 (551071155952324937537/500000000000000000000000) (601202263041088368201389/1000000000000000000000000) (63839739139039/10000000000000000000000) where
  r0 := (139528733803/250000000000000000)
  k0 := (176591823154331/50000000000000000)
  k6 := (1127392611197661/100000000000000000)
  q := (85883642214335553877/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14752]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14752]

theorem width_14753 : mW 14753 = 390014899516708 := by
  have hu : mW 14753 ≤ 390014899516708 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14753 ≤ 390014899516707 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14753 : RowArithmetic 14753 (275528981058210968459/250000000000000000000000) (300596007247177458071707/500000000000000000000000) (6382849204021999/1000000000000000000000000) where
  r0 := (69757273783/125000000000000000)
  k0 := (1765828456589173/500000000000000000)
  k6 := (2818386004056961/250000000000000000)
  q := (171773106160423145561/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14753]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14753]

theorem width_14754 : mW 14754 = 390107434445949 := by
  have hu : mW 14754 ≤ 390107434445949 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14754 ≤ 390107434445948 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14754 : RowArithmetic 14754 (551044771270919709271/500000000000000000000000) (601181767321592434441919/1000000000000000000000000) (797715596390037/125000000000000000000000) where
  r0 := (558001454931/1000000000000000000)
  k0 := (1765738692283477/500000000000000000)
  k6 := (2818290489831599/250000000000000000)
  q := (21472365961858977221/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14754]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14754]

theorem width_14755 : mW 14755 = 390199985056152 := by
  have hu : mW 14755 ≤ 390199985056152 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14755 ≤ 390199985056151 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14755 : RowArithmetic 14755 (275515791707465597131/250000000000000000000000) (150292880380626626243759/250000000000000000000000) (3190300307555617/500000000000000000000000) where
  r0 := (557944729211/1000000000000000000)
  k0 := (1765648938624681/500000000000000000)
  k6 := (2254555988253137/200000000000000000)
  q := (34356949806407436669/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14755]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14755]

theorem width_14756 : mW 14756 = 390292551348913 := by
  have hu : mW 14756 ≤ 390292551348913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14756 ≤ 390292551348912 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14756 : RowArithmetic 14756 (275509199273784510821/250000000000000000000000) (4809290216774422806393/8000000000000000000000) (1275895347181449/200000000000000000000000) where
  r0 := (557888013101/1000000000000000000)
  k0 := (141244735648773/40000000000000000)
  k6 := (11272397962039129/1000000000000000000)
  q := (171790570171939297863/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14756]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14756]

theorem width_14757 : mW 14757 = 390385133325825 := by
  have hu : mW 14757 ≤ 390385133325825 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14757 ≤ 390385133325824 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14757 : RowArithmetic 14757 (551005216667946804611/500000000000000000000000) (601151034044187247388359/1000000000000000000000000) (3189176566710421/500000000000000000000000) where
  r0 := (2789156533/5000000000000000)
  k0 := (3530938926476923/1000000000000000000)
  k6 := (225440320432803/20000000000000000)
  q := (34359278222919642699/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14757]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14757]

theorem width_14758 : mW 14758 = 390477730988482 := by
  have hu : mW 14758 ≤ 390477730988482 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14758 ≤ 390477730988481 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14758 : RowArithmetic 14758 (1101984075550356554431/1000000000000000000000000) (300570396182182760063059/500000000000000000000000) (3188614903782279/500000000000000000000000) where
  r0 := (69721826213/125000000000000000)
  k0 := (1765379741506371/500000000000000000)
  k6 := (1127163412006217/100000000000000000)
  q := (171802211860033979017/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14758]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14758]

theorem width_14759 : mW 14759 = 390570344338480 := by
  have hu : mW 14759 ≤ 390570344338480 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14759 ≤ 390570344338479 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14759 : RowArithmetic 14759 (550978861868377079401/500000000000000000000000) (601130552057043649912063/1000000000000000000000000) (398506672390683/62500000000000000000000) where
  r0 := (139429480603/250000000000000000)
  k0 := (3530580060826861/1000000000000000000)
  k6 := (2817813064324653/250000000000000000)
  q := (2684500506379166247/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14759]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14759]

theorem width_14760 : mW 14760 = 390662973377412 := by
  have hu : mW 14760 ≤ 390662973377412 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14760 ≤ 390662973377411 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14760 : RowArithmetic 14760 (220386275578663133321/200000000000000000000000) (601120313121927720616037/1000000000000000000000000) (796872998174071/125000000000000000000000) where
  r0 := (557661244721/1000000000000000000)
  k0 := (3530400659913029/1000000000000000000)
  k6 := (1408858804167863/125000000000000000)
  q := (85906926379658118927/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14760]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14760]

theorem width_14761 : mW 14761 = 390755618106873 := by
  have hu : mW 14761 ≤ 390755618106873 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14761 ≤ 390755618106872 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14761 : RowArithmetic 14761 (1101905038018270133251/1000000000000000000000000) (150277518889680957503169/250000000000000000000000) (6373861488902099/1000000000000000000000000) where
  r0 := (55760457663/100000000000000000)
  k0 := (882555320067831/250000000000000000)
  k6 := (1408811081023559/125000000000000000)
  q := (171819672913202811743/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14761]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14761]

theorem width_14762 : mW 14762 = 390848278528458 := by
  have hu : mW 14762 ≤ 390848278528458 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14762 ≤ 390848278528457 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14762 : RowArithmetic 14762 (1101878704109847286463/1000000000000000000000000) (150274959841784544690009/250000000000000000000000) (398296204293261/62500000000000000000000) where
  r0 := (111509583627/200000000000000000)
  k0 := (882510480473081/250000000000000000)
  k6 := (1408763362728593/125000000000000000)
  q := (171825492869946396671/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14762]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14762]

theorem width_14763 : mW 14763 = 390940954643762 := by
  have hu : mW 14763 ≤ 390940954643762 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14763 ≤ 390940954643761 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14763 : RowArithmetic 14763 (220370475233255505189/200000000000000000000000) (300544802273438544640427/500000000000000000000000) (199113041396109/31250000000000000000000) where
  r0 := (111498253847/200000000000000000)
  k0 := (1764931292388053/500000000000000000)
  k6 := (11269725194257151/1000000000000000000)
  q := (171831312629567024443/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14763]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14763]

theorem width_14764 : mW 14764 = 391033646454378 := by
  have hu : mW 14764 ≤ 391033646454378 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14764 ≤ 391033646454377 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14764 : RowArithmetic 14764 (275456513546448195547/250000000000000000000000) (601079371097646943876393/1000000000000000000000000) (637049565676479/100000000000000000000000) where
  r0 := (557434629927/1000000000000000000)
  k0 := (3529683268916413/1000000000000000000)
  k6 := (90154748203737/8000000000000000)
  q := (171837132192084723467/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14764]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14764]

theorem width_14765 : mW 14765 = 391126353961902 := by
  have hu : mW 14765 ≤ 391126353961902 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14765 ≤ 391126353961901 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14765 : RowArithmetic 14765 (1101799738166624367463/1000000000000000000000000) (601069139019154200883853/1000000000000000000000000) (254774970594913/40000000000000000000000) where
  r0 := (557378000209/1000000000000000000)
  k0 := (3529503974310151/1000000000000000000)
  k6 := (112689618954521/10000000000000000)
  q := (34368590311503903753/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14765]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14765]

theorem width_14766 : mW 14766 = 391219077167929 := by
  have hu : mW 14766 ≤ 391219077167929 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14766 ≤ 391219077167928 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14766 : RowArithmetic 14766 (1101773428107004694941/1000000000000000000000000) (300529454155552712190303/500000000000000000000000) (3184126574456193/500000000000000000000000) where
  r0 := (278660690039/500000000000000000)
  k0 := (1764662350475531/500000000000000000)
  k6 := (1126858030420551/100000000000000000)
  q := (42962192681472857991/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14766]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14766]

theorem width_14767 : mW 14767 = 391311816074054 := by
  have hu : mW 14767 ≤ 391311816074054 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14767 ≤ 391311816074053 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14767 : RowArithmetic 14767 (55087356200258342423/50000000000000000000000) (601048678973207268957141/1000000000000000000000000) (63671323087963/10000000000000000000000) where
  r0 := (557264769533/1000000000000000000)
  k0 := (220571590552451/62500000000000000)
  k6 := (11268198751720791/1000000000000000000)
  q := (34370917939444096261/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14767]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14767]

theorem width_14768 : mW 14768 = 391404570681870 := by
  have hu : mW 14768 ≤ 391404570681870 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14768 ≤ 391404570681869 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14768 : RowArithmetic 14768 (1101720825859345439969/1000000000000000000000000) (24041538040206660157989/40000000000000000000000) (318300587221873/50000000000000000000000) where
  r0 := (139302042143/250000000000000000)
  k0 := (3528966217971519/1000000000000000000)
  k6 := (5633908618995691/500000000000000000)
  q := (42965102117881670409/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14768]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14768]

theorem width_14769 : mW 14769 = 391497340992975 := by
  have hu : mW 14769 ≤ 391497340992975 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14769 ≤ 391497340992974 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14769 : RowArithmetic 14769 (1101694533667773606483/1000000000000000000000000) (601028224406689882969199/1000000000000000000000000) (1272978291149743/200000000000000000000000) where
  r0 := (557151577191/1000000000000000000)
  k0 := (3528787008338539/1000000000000000000)
  k6 := (11267435763010723/1000000000000000000)
  q := (171866227048830044421/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14769]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14769]

theorem width_14770 : mW 14770 = 391590127008961 := by
  have hu : mW 14770 ≤ 391590127008961 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14770 ≤ 391590127008960 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14770 : RowArithmetic 14770 (1101668247428687728021/1000000000000000000000000) (120203599835496865474181/200000000000000000000000) (1590942860660761/250000000000000000000000) where
  r0 := (139273748847/250000000000000000)
  k0 := (1764303909968589/500000000000000000)
  k6 := (2253410865354451/200000000000000000)
  q := (85936022714575288867/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14770]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14770]

theorem width_14771 : mW 14771 = 391682928731425 := by
  have hu : mW 14771 ≤ 391682928731425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14771 ≤ 391682928731424 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14771 : RowArithmetic 14771 (44065678685612908401/40000000000000000000000) (601007775317256837199293/1000000000000000000000000) (6362651705033379/1000000000000000000000000) where
  r0 := (278519211581/500000000000000000)
  k0 := (220526790797969/62500000000000000)
  k6 := (563333646463471/50000000000000000)
  q := (85938931806254143131/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14771]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14771]

theorem width_14772 : mW 14772 = 391775746161962 := by
  have hu : mW 14772 ≤ 391775746161962 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14772 ≤ 391775746161961 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14772 : RowArithmetic 14772 (34425490400028593273/31250000000000000000000) (600997552825714491598167/1000000000000000000000000) (79519153035409/12500000000000000000000) where
  r0 := (556981860511/1000000000000000000)
  k0 := (3528249506826417/1000000000000000000)
  k6 := (5633145785247831/500000000000000000)
  q := (171883681598923171309/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14772]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14772]

theorem width_14773 : mW 14773 = 391868579302166 := by
  have hu : mW 14773 ≤ 391868579302166 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14773 ≤ 391868579302165 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14773 : RowArithmetic 14773 (550794712204351040567/500000000000000000000000) (150246832925641119196599/250000000000000000000000) (3180206527977059/500000000000000000000000) where
  r0 := (55692530743/100000000000000000)
  k0 := (3528070382101313/1000000000000000000)
  k6 := (11265910250444429/1000000000000000000)
  q := (171889499388415230791/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14773]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14773]

theorem width_14774 : mW 14774 = 391961428153634 := by
  have hu : mW 14774 ≤ 391961428153634 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14774 ≤ 391961428153633 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14774 : RowArithmetic 14774 (68847697622620057017/62500000000000000000000) (600977111947513983942263/1000000000000000000000000) (6359294144310607/1000000000000000000000000) where
  r0 := (6960859549/12500000000000000)
  k0 := (3527891278598591/1000000000000000000)
  k6 := (5632764484554583/500000000000000000)
  q := (171895316981004459243/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14774]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14774]

theorem width_14775 : mW 14775 = 392054292717960 := by
  have hu : mW 14775 ≤ 392054292717960 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14775 ≤ 392054292717959 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14775 : RowArithmetic 14775 (275384226364702585927/250000000000000000000000) (150241723390067598077037/250000000000000000000000) (6358175507815307/1000000000000000000000000) where
  r0 := (556812229977/1000000000000000000)
  k0 := (1763856098154407/500000000000000000)
  k6 := (2816286931620831/250000000000000000)
  q := (171901134376710847813/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14775]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14775]

theorem width_14776 : mW 14776 = 392147172996739 := by
  have hu : mW 14776 ≤ 392147172996739 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14776 ≤ 392147172996738 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14776 : RowArithmetic 14776 (220302130979521896101/200000000000000000000000) (120191335308108225257977/200000000000000000000000) (1271411429276271/200000000000000000000000) where
  r0 := (278377852799/500000000000000000)
  k0 := (3527533135225707/1000000000000000000)
  k6 := (352023953830011/31250000000000000)
  q := (17190695157555438427/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14776]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14776]

theorem width_14777 : mW 14777 = 392240068991568 := by
  have hu : mW 14777 ≤ 392240068991568 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14777 ≤ 392240068991567 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14777 : RowArithmetic 14777 (550742205138278620187/500000000000000000000000) (300473230444016829747633/500000000000000000000000) (6355939059921891/1000000000000000000000000) where
  r0 := (556699190783/1000000000000000000)
  k0 := (1410941638141/400000000000000)
  k6 := (5632192678666851/500000000000000000)
  q := (85956384288777526499/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14777]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14777]

theorem width_14778 : mW 14778 = 392332980704041 := by
  have hu : mW 14778 ≤ 392332980704041 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14778 ≤ 392332980704040 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14778 : RowArithmetic 14778 (220291634318778898207/200000000000000000000000) (150234061650613902691099/250000000000000000000000) (1270964249670027/200000000000000000000000) where
  r0 := (69580335691/125000000000000000)
  k0 := (14108700306719/4000000000000000)
  k6 := (11264004230796829/1000000000000000000)
  q := (42979646345683208751/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14778]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14778]

theorem width_14779 : mW 14779 = 392425908135754 := by
  have hu : mW 14779 ≤ 392425908135754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14779 ≤ 392425908135753 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14779 : RowArithmetic 14779 (220286387769572382441/200000000000000000000000) (150231508420878659545639/250000000000000000000000) (397106481973707/62500000000000000000000) where
  r0 := (556586189831/1000000000000000000)
  k0 := (3526996079204349/1000000000000000000)
  k6 := (11263623142943187/1000000000000000000)
  q := (17192440199110770791/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14779]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14779]

theorem width_14780 : mW 14780 = 392518851288303 := by
  have hu : mW 14780 ≤ 392518851288303 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14780 ≤ 392518851288302 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14780 : RowArithmetic 14780 (27535142800917521267/25000000000000000000000) (150228955532729629945957/250000000000000000000000) (158814661238067/25000000000000000000000) where
  r0 := (55652970369/100000000000000000)
  k0 := (3526817102923187/1000000000000000000)
  k6 := (11263242093766233/1000000000000000000)
  q := (171930218402699645963/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14780]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14780]

theorem width_14781 : mW 14781 = 392611810163284 := by
  have hu : mW 14781 ≤ 392611810163284 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14781 ≤ 392611810163283 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14781 : RowArithmetic 14781 (1101379491158653320007/1000000000000000000000000) (30045280597218755471949/50000000000000000000000) (1587867365523383/250000000000000000000000) where
  r0 := (556473227103/1000000000000000000)
  k0 := (3526638147833153/1000000000000000000)
  k6 := (5631430541629713/500000000000000000)
  q := (17193603461752862003/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14781]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14781]

theorem width_14782 : mW 14782 = 392704784762291 := by
  have hu : mW 14782 ≤ 392704784762291 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14782 ≤ 392704784762290 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14782 : RowArithmetic 14782 (55067663810598142661/50000000000000000000000) (300447701561796164167237/500000000000000000000000) (6350352749205227/1000000000000000000000000) where
  r0 := (556416760067/1000000000000000000)
  k0 := (3526459213927967/1000000000000000000)
  k6 := (450499204456649/40000000000000000)
  q := (85970925317807298799/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14782]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14782]

theorem width_14783 : mW 14783 = 392797775086920 := by
  have hu : mW 14783 ≤ 392797775086920 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14783 ≤ 392797775086919 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14783 : RowArithmetic 14783 (220265413438974559077/200000000000000000000000) (75110649458534776631867/125000000000000000000000) (50793890486169/8000000000000000000000) where
  r0 := (27818015129/50000000000000000)
  k0 := (705256060240903/200000000000000000)
  k6 := (11262099178230091/1000000000000000000)
  q := (171947666456977542781/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14783]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14783]

theorem width_14784 : mW 14784 = 392890781138768 := by
  have hu : mW 14784 ≤ 392890781138768 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14784 ≤ 392890781138767 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14784 : RowArithmetic 14784 (68831304006601670697/62500000000000000000000) (150218747394535218283083/250000000000000000000000) (3174060073352303/500000000000000000000000) where
  r0 := (6953798183/12500000000000000)
  k0 := (3526101409659683/1000000000000000000)
  k6 := (11261718283694487/1000000000000000000)
  q := (85976741040818708157/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14784]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14784]

theorem width_14785 : mW 14785 = 392983802919431 := by
  have hu : mW 14785 ≤ 392983802919431 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14785 ≤ 392983802919430 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14785 : RowArithmetic 14785 (550637333471234668657/500000000000000000000000) (2347128065831595575887/3906250000000000000000) (6347004256919099/1000000000000000000000000) where
  r0 := (111249483249/200000000000000000)
  k0 := (881480634822589/250000000000000000)
  k6 := (11261337427802879/1000000000000000000)
  q := (85979648754807087779/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14785]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14785]

theorem width_14786 : mW 14786 = 393076840430503 := by
  have hu : mW 14786 ≤ 393076840430503 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14786 ≤ 393076840430502 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14786 : RowArithmetic 14786 (550624237851823403751/500000000000000000000000) (600854581492229292682699/1000000000000000000000000) (63458886413281/10000000000000000000000) where
  r0 := (556190987393/1000000000000000000)
  k0 := (1762871845046709/500000000000000000)
  k6 := (2815239152637183/250000000000000000)
  q := (171965112740927774499/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14786]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14786]

theorem width_14787 : mW 14787 = 393169893673582 := by
  have hu : mW 14787 ≤ 393169893673582 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14787 ≤ 393169893673581 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14787 : RowArithmetic 14787 (550611145193702148021/500000000000000000000000) (600844379495871719684871/1000000000000000000000000) (1586193324961269/250000000000000000000000) where
  r0 := (6951682101/12500000000000000)
  k0 := (881391215514853/250000000000000000)
  k6 := (11260575831925513/1000000000000000000)
  q := (42992731943899540937/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14787]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14787]

theorem width_14788 : mW 14788 = 393262962650263 := by
  have hu : mW 14788 ≤ 393262962650263 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14788 ≤ 393262962650262 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14788 : RowArithmetic 14788 (1101196110991988899641/1000000000000000000000000) (30041708943176209100179/50000000000000000000000) (6343658232383573/1000000000000000000000000) where
  r0 := (111215631661/200000000000000000)
  k0 := (3525386055188389/1000000000000000000)
  k6 := (11260195091926691/1000000000000000000)
  q := (85988371306822645273/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14788]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14788]

theorem width_14789 : mW 14789 = 393356047362142 := by
  have hu : mW 14789 ≤ 393356047362142 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14789 ≤ 393356047362141 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14789 : RowArithmetic 14789 (70474876001001469/64000000000000000000) (600823979594895258185969/1000000000000000000000000) (6342543438857159/1000000000000000000000000) where
  r0 := (278010879033/500000000000000000)
  k0 := (3525207269477229/1000000000000000000)
  k6 := (5629907195272869/500000000000000000)
  q := (4299563931377227469/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14789]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14789]

theorem width_14790 : mW 14790 = 393449147810815 := by
  have hu : mW 14790 ≤ 393449147810815 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14790 ≤ 393449147810814 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14790 : RowArithmetic 14790 (550571884978314727571/500000000000000000000000) (300406890844846768116773/500000000000000000000000) (6341428919179433/1000000000000000000000000) where
  r0 := (1737391773/3125000000000000)
  k0 := (1762514252459821/500000000000000000)
  k6 := (90075469822209/8000000000000000)
  q := (34397674339989905777/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14790]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14790]

theorem width_14791 : mW 14791 = 393542263997878 := by
  have hu : mW 14791 ≤ 393542263997878 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14791 ≤ 393542263997877 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14791 : RowArithmetic 14791 (275279402078295516959/250000000000000000000000) (15020089628690692771991/25000000000000000000000) (6340314673264031/1000000000000000000000000) where
  r0 := (111181797237/200000000000000000)
  k0 := (440606220189063/125000000000000000)
  k6 := (5629526551805663/500000000000000000)
  q := (171994185948246518047/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14791]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14791]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14717 then ⟨(220613932432029238103/200000000000000000000000), (150390457518071315608247/250000000000000000000000), (1284702788052461/200000000000000000000000)⟩ else
  if n = 14718 then ⟨(1103043064037177127031/1000000000000000000000000), (300775766625213596062299/500000000000000000000000), (1284475896127431/200000000000000000000000)⟩ else
  if n = 14719 then ⟨(1103016471957533981409/1000000000000000000000000), (601541237812898563268073/1000000000000000000000000), (1284249060215747/200000000000000000000000)⟩ else
  if n = 14720 then ⟨(1102989885919419741003/1000000000000000000000000), (601530943759401898987151/1000000000000000000000000), (6420111401498299/1000000000000000000000000)⟩ else
  if n = 14721 then ⟨(551481652960518601273/500000000000000000000000), (75190081386204981750703/125000000000000000000000), (3134266495023/488281250000000000000)⟩ else
  if n = 14722 then ⟨(551468365980295141893/500000000000000000000000), (300755179901657598144781/500000000000000000000000), (6417844441916459/1000000000000000000000000)⟩ else
  if n = 14723 then ⟨(1102910164036283585713/1000000000000000000000000), (601500069900130714372767/1000000000000000000000000), (1283342276347541/200000000000000000000000)⟩ else
  if n = 14724 then ⟨(1102883602146321519417/1000000000000000000000000), (30074489068989464853431/50000000000000000000000), (6415578601182189/1000000000000000000000000)⟩ else
  if n = 14725 then ⟨(1102857046288910052397/1000000000000000000000000), (120295898848398800577049/200000000000000000000000), (256577844006453/40000000000000000000000)⟩ else
  if n = 14726 then ⟨(1102830496462255834389/1000000000000000000000000), (300734604243223938305159/500000000000000000000000), (20041605870583/3125000000000000000000)⟩ else
  if n = 14727 then ⟨(1102803952664565761137/1000000000000000000000000), (300729462056427038415837/500000000000000000000000), (3206090968184681/500000000000000000000000)⟩ else
  if n = 14728 then ⟨(1102777414894047410643/1000000000000000000000000), (601448641120915891409517/1000000000000000000000000), (6411050273421233/1000000000000000000000000)⟩ else
  if n = 14729 then ⟨(1102750883148909478363/1000000000000000000000000), (601438359510336679243149/1000000000000000000000000), (6409918889653729/1000000000000000000000000)⟩ else
  if n = 14730 then ⟨(1102724357427360469911/1000000000000000000000000), (601428079280819848886093/1000000000000000000000000), (1602196946244601/250000000000000000000000)⟩ else
  if n = 14731 then ⟨(34459307428987812751/31250000000000000000000), (300708900216034459802241/500000000000000000000000), (6407656959306867/1000000000000000000000000)⟩ else
  if n = 14732 then ⟨(110267132404786883141/100000000000000000000000), (601407522963787501736593/1000000000000000000000000), (3203263206275389/500000000000000000000000)⟩ else
  if n = 14733 then ⟨(220528963277269584753/200000000000000000000000), (601397246875679295489239/1000000000000000000000000), (1601349036155453/250000000000000000000000)⟩ else
  if n = 14734 then ⟨(55130915737062925719/50000000000000000000000), (300693486083724047607361/500000000000000000000000), (6404266155431669/1000000000000000000000000)⟩ else
  if n = 14735 then ⟨(1102591819110812947641/1000000000000000000000000), (300688349419398889615993/500000000000000000000000), (3201568222446047/500000000000000000000000)⟩ else
  if n = 14736 then ⟨(1102565329493224247513/1000000000000000000000000), (601366426889432281380663/1000000000000000000000000), (6402007012914871/1000000000000000000000000)⟩ else
  if n = 14737 then ⟨(137817355735838318921/125000000000000000000000), (601356156319055637288437/1000000000000000000000000), (1280175571882367/200000000000000000000000)⟩ else
  if n = 14738 then ⟨(1102512368289473372813/1000000000000000000000000), (30067294356368600526939/50000000000000000000000), (1279949796858961/200000000000000000000000)⟩ else
  if n = 14739 then ⟨(137810737087467471631/125000000000000000000000), (601335619314085613092551/1000000000000000000000000), (639862038747567/100000000000000000000000)⟩ else
  if n = 14740 then ⟨(1102459431115721491517/1000000000000000000000000), (601325352878900745140913/1000000000000000000000000), (6397492068866351/1000000000000000000000000)⟩ else
  if n = 14741 then ⟨(137804121441954314011/125000000000000000000000), (120263017564304357546273/200000000000000000000000), (639636402837879/100000000000000000000000)⟩ else
  if n = 14742 then ⟨(1102406517957695930199/1000000000000000000000000), (120260964828330655578327/200000000000000000000000), (319761813296249/50000000000000000000000)⟩ else
  if n = 14743 then ⟨(1102380070380123518533/1000000000000000000000000), (601294561838999737591981/1000000000000000000000000), (1598527195354237/250000000000000000000000)⟩ else
  if n = 14744 then ⟨(1102353628801134860743/1000000000000000000000000), (601284300913265819615147/1000000000000000000000000), (6392981574766723/1000000000000000000000000)⟩ else
  if n = 14745 then ⟨(551163596609474758411/500000000000000000000000), (30063702068207813400353/50000000000000000000000), (319592732294321/50000000000000000000000)⟩ else
  if n = 14746 then ⟨(137787595453973248977/125000000000000000000000), (75157972898921987893861/125000000000000000000000), (159768199867203/25000000000000000000000)⟩ else
  if n = 14747 then ⟨(1102274340037865198561/1000000000000000000000000), (30062676319731484249381/50000000000000000000000), (798700202635501/125000000000000000000000)⟩ else
  if n = 14748 then ⟨(551123961217703930109/500000000000000000000000), (601243270973622592351581/1000000000000000000000000), (6388475524986267/1000000000000000000000000)⟩ else
  if n = 14749 then ⟨(1102221510822635375881/1000000000000000000000000), (601233016928059643519689/1000000000000000000000000), (6387349706307119/1000000000000000000000000)⟩ else
  if n = 14750 then ⟨(1102195105197769388303/1000000000000000000000000), (601222764257646124741983/1000000000000000000000000), (6386224164958801/1000000000000000000000000)⟩ else
  if n = 14751 then ⟨(1102168705559033079733/1000000000000000000000000), (601212512962087253982581/1000000000000000000000000), (319254945042681/50000000000000000000000)⟩ else
  if n = 14752 then ⟨(551071155952324937537/500000000000000000000000), (601202263041088368201389/1000000000000000000000000), (63839739139039/10000000000000000000000)⟩ else
  if n = 14753 then ⟨(275528981058210968459/250000000000000000000000), (300596007247177458071707/500000000000000000000000), (6382849204021999/1000000000000000000000000)⟩ else
  if n = 14754 then ⟨(551044771270919709271/500000000000000000000000), (601181767321592434441919/1000000000000000000000000), (797715596390037/125000000000000000000000)⟩ else
  if n = 14755 then ⟨(275515791707465597131/250000000000000000000000), (150292880380626626243759/250000000000000000000000), (3190300307555617/500000000000000000000000)⟩ else
  if n = 14756 then ⟨(275509199273784510821/250000000000000000000000), (4809290216774422806393/8000000000000000000000), (1275895347181449/200000000000000000000000)⟩ else
  if n = 14757 then ⟨(551005216667946804611/500000000000000000000000), (601151034044187247388359/1000000000000000000000000), (3189176566710421/500000000000000000000000)⟩ else
  if n = 14758 then ⟨(1101984075550356554431/1000000000000000000000000), (300570396182182760063059/500000000000000000000000), (3188614903782279/500000000000000000000000)⟩ else
  if n = 14759 then ⟨(550978861868377079401/500000000000000000000000), (601130552057043649912063/1000000000000000000000000), (398506672390683/62500000000000000000000)⟩ else
  if n = 14760 then ⟨(220386275578663133321/200000000000000000000000), (601120313121927720616037/1000000000000000000000000), (796872998174071/125000000000000000000000)⟩ else
  if n = 14761 then ⟨(1101905038018270133251/1000000000000000000000000), (150277518889680957503169/250000000000000000000000), (6373861488902099/1000000000000000000000000)⟩ else
  if n = 14762 then ⟨(1101878704109847286463/1000000000000000000000000), (150274959841784544690009/250000000000000000000000), (398296204293261/62500000000000000000000)⟩ else
  if n = 14763 then ⟨(220370475233255505189/200000000000000000000000), (300544802273438544640427/500000000000000000000000), (199113041396109/31250000000000000000000)⟩ else
  if n = 14764 then ⟨(275456513546448195547/250000000000000000000000), (601079371097646943876393/1000000000000000000000000), (637049565676479/100000000000000000000000)⟩ else
  if n = 14765 then ⟨(1101799738166624367463/1000000000000000000000000), (601069139019154200883853/1000000000000000000000000), (254774970594913/40000000000000000000000)⟩ else
  if n = 14766 then ⟨(1101773428107004694941/1000000000000000000000000), (300529454155552712190303/500000000000000000000000), (3184126574456193/500000000000000000000000)⟩ else
  if n = 14767 then ⟨(55087356200258342423/50000000000000000000000), (601048678973207268957141/1000000000000000000000000), (63671323087963/10000000000000000000000)⟩ else
  if n = 14768 then ⟨(1101720825859345439969/1000000000000000000000000), (24041538040206660157989/40000000000000000000000), (318300587221873/50000000000000000000000)⟩ else
  if n = 14769 then ⟨(1101694533667773606483/1000000000000000000000000), (601028224406689882969199/1000000000000000000000000), (1272978291149743/200000000000000000000000)⟩ else
  if n = 14770 then ⟨(1101668247428687728021/1000000000000000000000000), (120203599835496865474181/200000000000000000000000), (1590942860660761/250000000000000000000000)⟩ else
  if n = 14771 then ⟨(44065678685612908401/40000000000000000000000), (601007775317256837199293/1000000000000000000000000), (6362651705033379/1000000000000000000000000)⟩ else
  if n = 14772 then ⟨(34425490400028593273/31250000000000000000000), (600997552825714491598167/1000000000000000000000000), (79519153035409/12500000000000000000000)⟩ else
  if n = 14773 then ⟨(550794712204351040567/500000000000000000000000), (150246832925641119196599/250000000000000000000000), (3180206527977059/500000000000000000000000)⟩ else
  if n = 14774 then ⟨(68847697622620057017/62500000000000000000000), (600977111947513983942263/1000000000000000000000000), (6359294144310607/1000000000000000000000000)⟩ else
  if n = 14775 then ⟨(275384226364702585927/250000000000000000000000), (150241723390067598077037/250000000000000000000000), (6358175507815307/1000000000000000000000000)⟩ else
  if n = 14776 then ⟨(220302130979521896101/200000000000000000000000), (120191335308108225257977/200000000000000000000000), (1271411429276271/200000000000000000000000)⟩ else
  if n = 14777 then ⟨(550742205138278620187/500000000000000000000000), (300473230444016829747633/500000000000000000000000), (6355939059921891/1000000000000000000000000)⟩ else
  if n = 14778 then ⟨(220291634318778898207/200000000000000000000000), (150234061650613902691099/250000000000000000000000), (1270964249670027/200000000000000000000000)⟩ else
  if n = 14779 then ⟨(220286387769572382441/200000000000000000000000), (150231508420878659545639/250000000000000000000000), (397106481973707/62500000000000000000000)⟩ else
  if n = 14780 then ⟨(27535142800917521267/25000000000000000000000), (150228955532729629945957/250000000000000000000000), (158814661238067/25000000000000000000000)⟩ else
  if n = 14781 then ⟨(1101379491158653320007/1000000000000000000000000), (30045280597218755471949/50000000000000000000000), (1587867365523383/250000000000000000000000)⟩ else
  if n = 14782 then ⟨(55067663810598142661/50000000000000000000000), (300447701561796164167237/500000000000000000000000), (6350352749205227/1000000000000000000000000)⟩ else
  if n = 14783 then ⟨(220265413438974559077/200000000000000000000000), (75110649458534776631867/125000000000000000000000), (50793890486169/8000000000000000000000)⟩ else
  if n = 14784 then ⟨(68831304006601670697/62500000000000000000000), (150218747394535218283083/250000000000000000000000), (3174060073352303/500000000000000000000000)⟩ else
  if n = 14785 then ⟨(550637333471234668657/500000000000000000000000), (2347128065831595575887/3906250000000000000000), (6347004256919099/1000000000000000000000000)⟩ else
  if n = 14786 then ⟨(550624237851823403751/500000000000000000000000), (600854581492229292682699/1000000000000000000000000), (63458886413281/10000000000000000000000)⟩ else
  if n = 14787 then ⟨(550611145193702148021/500000000000000000000000), (600844379495871719684871/1000000000000000000000000), (1586193324961269/250000000000000000000000)⟩ else
  if n = 14788 then ⟨(1101196110991988899641/1000000000000000000000000), (30041708943176209100179/50000000000000000000000), (6343658232383573/1000000000000000000000000)⟩ else
  if n = 14789 then ⟨(70474876001001469/64000000000000000000), (600823979594895258185969/1000000000000000000000000), (6342543438857159/1000000000000000000000000)⟩ else
  if n = 14790 then ⟨(550571884978314727571/500000000000000000000000), (300406890844846768116773/500000000000000000000000), (6341428919179433/1000000000000000000000000)⟩ else
  ⟨(275279402078295516959/250000000000000000000000), (15020089628690692771991/25000000000000000000000), (6340314673264031/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14717 ≤ n) (hb : n ≤ 14791) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14717
  · exact row_14718
  · exact row_14719
  · exact row_14720
  · exact row_14721
  · exact row_14722
  · exact row_14723
  · exact row_14724
  · exact row_14725
  · exact row_14726
  · exact row_14727
  · exact row_14728
  · exact row_14729
  · exact row_14730
  · exact row_14731
  · exact row_14732
  · exact row_14733
  · exact row_14734
  · exact row_14735
  · exact row_14736
  · exact row_14737
  · exact row_14738
  · exact row_14739
  · exact row_14740
  · exact row_14741
  · exact row_14742
  · exact row_14743
  · exact row_14744
  · exact row_14745
  · exact row_14746
  · exact row_14747
  · exact row_14748
  · exact row_14749
  · exact row_14750
  · exact row_14751
  · exact row_14752
  · exact row_14753
  · exact row_14754
  · exact row_14755
  · exact row_14756
  · exact row_14757
  · exact row_14758
  · exact row_14759
  · exact row_14760
  · exact row_14761
  · exact row_14762
  · exact row_14763
  · exact row_14764
  · exact row_14765
  · exact row_14766
  · exact row_14767
  · exact row_14768
  · exact row_14769
  · exact row_14770
  · exact row_14771
  · exact row_14772
  · exact row_14773
  · exact row_14774
  · exact row_14775
  · exact row_14776
  · exact row_14777
  · exact row_14778
  · exact row_14779
  · exact row_14780
  · exact row_14781
  · exact row_14782
  · exact row_14783
  · exact row_14784
  · exact row_14785
  · exact row_14786
  · exact row_14787
  · exact row_14788
  · exact row_14789
  · exact row_14790
  · exact row_14791

end BstLean.Part271.R3.Rows14717
