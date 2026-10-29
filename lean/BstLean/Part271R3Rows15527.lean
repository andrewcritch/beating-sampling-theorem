import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15527–15601. -/
namespace BstLean.Part271.R3.Rows15527
open Real BstLean.Part130 BstLean.Part227

theorem width_15527 : mW 15527 = 466451437180645 := by
  have hu : mW 15527 ≤ 466451437180645 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15527 ≤ 466451437180644 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15527 : RowArithmetic 15527 (67709850102597984067/62500000000000000000000) (296825098983093709162089/500000000000000000000000) (5589100106148017/1000000000000000000000000) where
  r0 := (129213734691/250000000000000000)
  k0 := (212423772002153/62500000000000000)
  k6 := (2747241688861411/250000000000000000)
  q := (88110725794309514359/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15527]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15527]

theorem width_15528 : mW 15528 = 466556590234365 := by
  have hu : mW 15528 ≤ 466556590234365 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15528 ≤ 466556590234364 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15528 : RowArithmetic 15528 (1083335363174888101811/1000000000000000000000000) (593640932192383779496103/1000000000000000000000000) (5588166189494173/1000000000000000000000000) where
  r0 := (25840250577/50000000000000000)
  k0 := (849654047536371/250000000000000000)
  k6 := (10988612906151371/1000000000000000000)
  q := (176227126175285511861/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15528]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15528]

theorem width_15529 : mW 15529 = 466661760219034 := by
  have hu : mW 15529 ≤ 466661760219034 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15529 ≤ 466661760219033 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15529 : RowArithmetic 15529 (1083313129488790236979/1000000000000000000000000) (37101979224254429660103/62500000000000000000000) (1117446498201429/200000000000000000000000) where
  r0 := (258377546177/500000000000000000)
  k0 := (679690409351549/200000000000000000)
  k6 := (549412954551859/50000000000000000)
  q := (88116400289616915331/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15529]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15529]

theorem width_15530 : mW 15530 = 466766947136290 := by
  have hu : mW 15530 ≤ 466766947136290 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15530 ≤ 466766947136289 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15530 : RowArithmetic 15530 (1083290900581927702163/1000000000000000000000000) (593622404153012831539999/1000000000000000000000000) (1117259802124293/200000000000000000000000) where
  r0 := (129176295301/250000000000000000)
  k0 := (1699143960933667/500000000000000000)
  k6 := (343372040940549/31250000000000000)
  q := (176238474800481634219/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15530]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15530]

theorem width_15531 : mW 15531 = 466872150987767 := by
  have hu : mW 15531 ≤ 466872150987767 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15531 ≤ 466872150987766 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15531 : RowArithmetic 15531 (6770429227830973841/6250000000000000000000) (148403285471743429224589/250000000000000000000000) (698170718533967/125000000000000000000000) where
  r0 := (64581909761/125000000000000000)
  k0 := (679624763094071/200000000000000000)
  k6 := (5493775781663517/500000000000000000)
  q := (88122074419523284393/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15531]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15531]

theorem width_15532 : mW 15532 = 466977371775102 := by
  have hu : mW 15532 ≤ 466977371775102 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15532 ≤ 466977371775101 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15532 : RowArithmetic 15532 (5416232285502647079/5000000000000000000000) (296801940394858843601973/500000000000000000000000) (111688654077851/20000000000000000000000) where
  r0 := (129151345751/250000000000000000)
  k0 := (339795972756291/100000000000000000)
  k6 := (5493598925360039/500000000000000000)
  q := (88124911347473138891/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15532]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15532]

theorem width_15533 : mW 15533 = 467082609499929 := by
  have hu : mW 15533 ≤ 467082609499929 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15533 ≤ 467082609499928 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15533 : RowArithmetic 15533 (1083224242523304791559/1000000000000000000000000) (74199327607626132297739/125000000000000000000000) (2791749938709279/500000000000000000000000) where
  r0 := (516555495951/1000000000000000000)
  k0 := (849448914536097/250000000000000000)
  k6 := (10986844172271201/1000000000000000000)
  q := (176255496368198401781/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15533]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15533]

theorem width_15534 : mW 15534 = 467187864163885 := by
  have hu : mW 15534 ≤ 467187864163885 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15534 ≤ 467187864163884 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15534 : RowArithmetic 15534 (270800508179984438053/250000000000000000000000) (593585362100612099450919/1000000000000000000000000) (5582567268784403/1000000000000000000000000) where
  r0 := (258252808463/500000000000000000)
  k0 := (3397631607207601/1000000000000000000)
  k6 := (10986490527974907/1000000000000000000)
  q := (176261169858820578521/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15534]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15534]

theorem width_15535 : mW 15535 = 467293135768605 := by
  have hu : mW 15535 ≤ 467293135768605 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15535 ≤ 467293135768604 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15535 : RowArithmetic 15535 (541589913844542615789/500000000000000000000000) (118715220901658231260699/200000000000000000000000) (2790817438962387/500000000000000000000000) where
  r0 := (64556968241/125000000000000000)
  k0 := (53085430855499/15625000000000000)
  k6 := (10986136917825699/1000000000000000000)
  q := (176266843166830442899/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15535]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15535]

theorem width_15536 : mW 15536 = 467398424315726 := by
  have hu : mW 15536 ≤ 467398424315726 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15536 ≤ 467398424315725 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15536 : RowArithmetic 15536 (270789406857351002059/250000000000000000000000) (4748534784670485507799/8000000000000000000000) (139517567619359/25000000000000000000000) where
  r0 := (258202941477/500000000000000000)
  k0 := (3397303560770203/1000000000000000000)
  k6 := (5492891670909041/500000000000000000)
  q := (88136258146122813489/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15536]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15536]

theorem width_15537 : mW 15537 = 467503729806883 := by
  have hu : mW 15537 ≤ 467503729806883 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15537 ≤ 467503729806882 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15537 : RowArithmetic 15537 (1083135431939551983279/1000000000000000000000000) (296778796413467597019253/500000000000000000000000) (5579770749267901/1000000000000000000000000) where
  r0 := (129089007001/250000000000000000)
  k0 := (1698569782632539/500000000000000000)
  k6 := (10985429799946563/1000000000000000000)
  q := (176278189235083759979/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15537]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15537]

theorem width_15538 : mW 15538 = 467609052243712 := by
  have hu : mW 15538 ≤ 467609052243712 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15538 ≤ 467609052243711 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15538 : RowArithmetic 15538 (216622648243637444333/200000000000000000000000) (593548338737429247851251/1000000000000000000000000) (1394709752835037/250000000000000000000000) where
  r0 := (20652247243/40000000000000000)
  k0 := (3396975588229367/1000000000000000000)
  k6 := (686567268262853/62500000000000000)
  q := (17628386199536246829/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15538]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15538]

theorem width_15539 : mW 15539 = 467714391627849 := by
  have hu : mW 15539 ≤ 467714391627849 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15539 ≤ 467714391627848 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15539 : RowArithmetic 15539 (216618211052793654309/200000000000000000000000) (593539085815057511901407/1000000000000000000000000) (1394476872731469/250000000000000000000000) where
  r0 := (258128171083/500000000000000000)
  k0 := (679362325932491/200000000000000000)
  k6 := (10984722818589847/1000000000000000000)
  q := (88144767286549687731/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15539]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15539]

theorem width_15540 : mW 15540 = 467819747960931 := by
  have hu : mW 15540 ≤ 467819747960931 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15540 ≤ 467819747960930 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15540 : RowArithmetic 15540 (541534437037776922601/500000000000000000000000) (74191229257448078840697/125000000000000000000000) (5576976187959873/1000000000000000000000000) where
  r0 := (20648260451/40000000000000000)
  k0 := (3396647689560437/1000000000000000000)
  k6 := (1098436937909367/100000000000000000)
  q := (176295206968312102209/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15540]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15540]

theorem width_15541 : mW 15541 = 467925121244593 := by
  have hu : mW 15541 ≤ 467925121244593 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15541 ≤ 467925121244592 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15541 : RowArithmetic 15541 (1083046697651603775577/1000000000000000000000000) (11870411669415507308267/20000000000000000000000) (348502818898561/62500000000000000000000) where
  r0 := (516156688399/1000000000000000000)
  k0 := (849120941979029/250000000000000000)
  k6 := (10984015973711629/1000000000000000000)
  q := (176300879181018266413/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15541]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15541]

theorem width_15542 : mW 15542 = 468030511480472 := by
  have hu : mW 15542 ≤ 468030511480472 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15542 ≤ 468030511480471 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15542 : RowArithmetic 15542 (135378065748847217557/125000000000000000000000) (296755667024197293102471/500000000000000000000000) (5575114234112023/1000000000000000000000000) where
  r0 := (516106873537/1000000000000000000)
  k0 := (3396319864728873/1000000000000000000)
  k6 := (5491831301219117/500000000000000000)
  q := (2203831890140443539/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15542]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15542]

theorem width_15543 : mW 15543 = 468135918670204 := by
  have hu : mW 15543 ≤ 468135918670204 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15543 ≤ 468135918670203 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15543 : RowArithmetic 15543 (270750589772934054719/250000000000000000000000) (593502085792207163551331/1000000000000000000000000) (2787091791549943/500000000000000000000000) where
  r0 := (8063391667/15625000000000000)
  k0 := (849038994999523/250000000000000000)
  k6 := (10983309265268001/1000000000000000000)
  q := (2754878485296583821/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15543]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15543]

theorem width_15544 : mW 15544 = 468241342815425 := by
  have hu : mW 15544 ≤ 468241342815425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15544 ≤ 468241342815424 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15544 : RowArithmetic 15544 (216596039390628034389/200000000000000000000000) (23739713548079121846679/40000000000000000000000) (696656643659433/125000000000000000000000) where
  r0 := (516007267849/1000000000000000000)
  k0 := (848998028429143/250000000000000000)
  k6 := (2745738990548861/250000000000000000)
  q := (35263578944854704013/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15544]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15544]

theorem width_15545 : mW 15545 = 468346783917771 := by
  have hu : mW 15545 ≤ 468346783917771 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15545 ≤ 468346783917770 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15545 : RowArithmetic 15545 (135369754946706380327/125000000000000000000000) (74185449097184038507591/125000000000000000000000) (69654036657171/12500000000000000000000) where
  r0 := (515957477019/1000000000000000000)
  k0 := (1697914132941847/500000000000000000)
  k6 := (274565067330377/25000000000000000)
  q := (176323566207129556231/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15545]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15545]

theorem width_15546 : mW 15546 = 468452241978880 := by
  have hu : mW 15546 ≤ 468452241978880 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15546 ≤ 468452241978879 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15546 : RowArithmetic 15546 (541467943475965059611/500000000000000000000000) (593474348018454989553573/1000000000000000000000000) (348212058308091/62500000000000000000000) where
  r0 := (128976923549/250000000000000000)
  k0 := (424458054561943/125000000000000000)
  k6 := (5491124729160713/500000000000000000)
  q := (176329237507567076759/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15546]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15546]

theorem width_15547 : mW 15547 = 468557717000386 := by
  have hu : mW 15547 ≤ 468557717000386 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15547 ≤ 468557717000385 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15547 : RowArithmetic 15547 (135364217385830055557/125000000000000000000000) (74183138053086405201237/125000000000000000000000) (1392615787569447/250000000000000000000000) where
  r0 := (257928959689/500000000000000000)
  k0 := (3395500625548213/1000000000000000000)
  k6 := (10981896257509/1000000000000000)
  q := (22041863578200460317/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15547]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15547]

theorem width_15548 : mW 15548 = 468663208983928 := by
  have hu : mW 15548 ≤ 468663208983928 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15548 ≤ 468663208983927 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15548 : RowArithmetic 15548 (541445797988221975907/500000000000000000000000) (118691172399189260726903/200000000000000000000000) (1113906716910727/200000000000000000000000) where
  r0 := (515808152563/1000000000000000000)
  k0 := (679067366607557/200000000000000000)
  k6 := (10981543090772323/1000000000000000000)
  q := (5510643111289280363/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15548]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15548]

theorem width_15549 : mW 15549 = 468768717931141 := by
  have hu : mW 15549 ≤ 468768717931141 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15549 ≤ 468768717931140 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15549 : RowArithmetic 15549 (1082869457620004328231/1000000000000000000000000) (593446620731985466805109/1000000000000000000000000) (556860423569203/100000000000000000000000) where
  r0 := (82521343/160000000000000)
  k0 := (3395173058963637/1000000000000000000)
  k6 := (2196237991621183/200000000000000000)
  q := (176346250314544539227/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15549]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15549]

theorem width_15550 : mW 15550 = 468874243843662 := by
  have hu : mW 15550 ≤ 468874243843662 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15550 ≤ 468874243843661 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15550 : RowArithmetic 15550 (1082847324015985105597/1000000000000000000000000) (593437380632574065034991/1000000000000000000000000) (2783837551814003/500000000000000000000000) where
  r0 := (64463580367/125000000000000000)
  k0 := (848752325829641/250000000000000000)
  k6 := (10980836859504299/1000000000000000000)
  q := (35270384177096795553/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15550]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15550]

theorem width_15551 : mW 15551 = 468979786723127 := by
  have hu : mW 15551 ≤ 468979786723127 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15551 ≤ 468979786723126 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15551 : RowArithmetic 15551 (135353149395381326789/125000000000000000000000) (593428141697477504601627/1000000000000000000000000) (556674618829663/100000000000000000000000) where
  r0 := (12891472503/25000000000000000)
  k0 := (169742278305097/50000000000000000)
  k6 := (10980483794961999/1000000000000000000)
  q := (176357591274092876799/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15551]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15551]

theorem width_15552 : mW 15552 = 469085346571174 := by
  have hu : mW 15552 ≤ 469085346571174 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15552 ≤ 469085346571173 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15552 : RowArithmetic 15552 (1082803071059865030233/1000000000000000000000000) (296709451963230641595991/500000000000000000000000) (5565817489632973/1000000000000000000000000) where
  r0 := (5156091653/10000000000000000)
  k0 := (424335230913731/125000000000000000)
  k6 := (549006538223677/50000000000000000)
  q := (176363261480388823071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15552]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15552]

theorem width_15553 : mW 15553 = 469190923389439 := by
  have hu : mW 15553 ≤ 469190923389439 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15553 ≤ 469190923389438 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15553 : RowArithmetic 15553 (1082780951705093644807/1000000000000000000000000) (593409667319290941253969/1000000000000000000000000) (5564889007572153/1000000000000000000000000) where
  r0 := (20622377539/40000000000000000)
  k0 := (1697259073470831/500000000000000000)
  k6 := (10979777768033447/1000000000000000000)
  q := (88184465752194700247/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15553]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15553]

theorem width_15554 : mW 15554 = 469296517179559 := by
  have hu : mW 15554 ≤ 469296517179559 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15554 ≤ 469296517179558 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15554 : RowArithmetic 15554 (54137941854870095607/50000000000000000000000) (593400431875732047356041/1000000000000000000000000) (5563960742049299/1000000000000000000000000) where
  r0 := (257754859821/500000000000000000)
  k0 := (339435446499017/100000000000000000)
  k6 := (1372428100704531/125000000000000000)
  q := (176374601346112190157/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15554]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15554]

theorem width_15555 : mW 15555 = 469402127943171 := by
  have hu : mW 15555 ≤ 469402127943171 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15555 ≤ 469402127943170 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15555 : RowArithmetic 15555 (1082736727235455766421/1000000000000000000000000) (593391197595550349835541/1000000000000000000000000) (2781516346499783/500000000000000000000000) where
  r0 := (644325011/1250000000000000)
  k0 := (678838160290949/200000000000000000)
  k6 := (10979071877276471/1000000000000000000)
  q := (88190135502787385161/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15555]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15555]

theorem width_15556 : mW 15556 = 469507755681911 := by
  have hu : mW 15556 ≤ 469507755681911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15556 ≤ 469507755681910 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15556 : RowArithmetic 15556 (541357311058960969319/500000000000000000000000) (148345491119627872385297/250000000000000000000000) (1112420972071629/200000000000000000000000) where
  r0 := (257705152973/500000000000000000)
  k0 := (3394027156328173/1000000000000000000)
  k6 := (10978718982948647/1000000000000000000)
  q := (22048242560349339553/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15556]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15556]

theorem width_15557 : mW 15557 = 469613400397418 := by
  have hu : mW 15557 ≤ 469613400397418 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15557 ≤ 469613400397417 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15557 : RowArithmetic 15557 (1082692521743466688491/1000000000000000000000000) (296686366262190695858227/500000000000000000000000) (1112235448812043/200000000000000000000000) where
  r0 := (12884015277/25000000000000000)
  k0 := (3393863529613117/1000000000000000000)
  k6 := (2195673224529461/200000000000000000)
  q := (88195804888894800539/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15557]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15557]

theorem width_15558 : mW 15558 = 469719062091327 := by
  have hu : mW 15558 ≤ 469719062091327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15558 ≤ 469719062091326 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15558 : RowArithmetic 15558 (1082670426110758022833/1000000000000000000000000) (296681750866462906828963/500000000000000000000000) (2780124922020513/500000000000000000000000) where
  r0 := (515310924199/1000000000000000000)
  k0 := (3393699921302361/1000000000000000000)
  k6 := (10978013296366979/1000000000000000000)
  q := (176397278890576994071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15558]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15558]

theorem width_15559 : mW 15559 = 469824740765275 := by
  have hu : mW 15559 ≤ 469824740765275 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15559 ≤ 469824740765274 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15559 : RowArithmetic 15559 (216529667043692758721/200000000000000000000000) (593354272103910760262703/1000000000000000000000000) (694915332529479/125000000000000000000000) where
  r0 := (257630622651/500000000000000000)
  k0 := (135741453255811/40000000000000000)
  k6 := (5488830252051101/500000000000000000)
  q := (5512592119411701949/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15559]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15559]

theorem width_15560 : mW 15560 = 469930436420901 := by
  have hu : mW 15560 ≤ 469930436420901 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15560 ≤ 469930436420900 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15560 : RowArithmetic 15560 (541313124532625849397/500000000000000000000000) (37084065227318886735957/62500000000000000000000) (5558395692579883/1000000000000000000000000) where
  r0 := (257605787193/500000000000000000)
  k0 := (3393372759884641/1000000000000000000)
  k6 := (10977307745847509/1000000000000000000)
  q := (176408616569599570113/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15560]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15560]

theorem width_15561 : mW 15561 = 470036149059841 := by
  have hu : mW 15561 ≤ 470036149059841 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15561 ≤ 470036149059840 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15561 : RowArithmetic 15561 (1082604167649790865107/1000000000000000000000000) (593335816332266129068597/1000000000000000000000000) (5557468941008493/1000000000000000000000000) where
  r0 := (10303238229/20000000000000000)
  k0 := (135728368270793/40000000000000000)
  k6 := (2195391004319487/200000000000000000)
  q := (88207142567934939313/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15561]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15561]

theorem width_15562 : mW 15562 = 470141878683732 := by
  have hu : mW 15562 ≤ 470141878683732 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15562 ≤ 470141878683731 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15562 : RowArithmetic 15562 (27064552274268764527/25000000000000000000000) (593326590189168808563559/1000000000000000000000000) (1111308481091397/200000000000000000000000) where
  r0 := (128778064123/250000000000000000)
  k0 := (3393045672046901/1000000000000000000)
  k6 := (10976602331346517/1000000000000000000)
  q := (88209976760001473203/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15562]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15562]

theorem width_15563 : mW 15563 = 470247625294212 := by
  have hu : mW 15563 ≤ 470247625294212 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15563 ≤ 470247625294211 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15563 : RowArithmetic 15563 (6766000118917501859/6250000000000000000000) (148329341301894088355417/250000000000000000000000) (5555616085860697/1000000000000000000000000) where
  r0 := (515062609511/1000000000000000000)
  k0 := (1696441077857617/500000000000000000)
  k6 := (2195249935017859/200000000000000000)
  q := (176425621722016329133/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15563]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15563]

theorem width_15564 : mW 15564 = 470353388892917 := by
  have hu : mW 15564 ≤ 470353388892917 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15564 ≤ 470353388892916 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15564 : RowArithmetic 15564 (541268975908305287723/500000000000000000000000) (74163517673406872032723/125000000000000000000000) (2777344991077507/500000000000000000000000) where
  r0 := (64376621313/125000000000000000)
  k0 := (3392718657767603/1000000000000000000)
  k6 := (10975897052820307/1000000000000000000)
  q := (35286257948385515933/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15564]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15564]

theorem width_15565 : mW 15565 = 470459169481486 := by
  have hu : mW 15565 ≤ 470459169481486 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15565 ≤ 470459169481485 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15565 : RowArithmetic 15565 (108251588933885150613/100000000000000000000000) (74162364840996389012201/125000000000000000000000) (1388441023568827/250000000000000000000000) where
  r0 := (51496333947/100000000000000000)
  k0 := (3392555178203371/1000000000000000000)
  k6 := (5487772232267047/500000000000000000)
  q := (4410923939493856201/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15565]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15565]

theorem width_15566 : mW 15566 = 470564967061556 := by
  have hu : mW 15566 ≤ 470564967061556 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15566 ≤ 470564967061555 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15566 : RowArithmetic 15566 (541246915796097145303/500000000000000000000000) (148322424307372767322577/250000000000000000000000) (2776419211078501/500000000000000000000000) where
  r0 := (257456858203/500000000000000000)
  k0 := (3392391717015313/1000000000000000000)
  k6 := (10975191910225199/1000000000000000000)
  q := (4411065630887847037/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15566]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15566]

theorem width_15567 : mW 15567 = 470670781634765 := by
  have hu : mW 15567 ≤ 470670781634765 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15567 ≤ 470670781634764 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15567 : RowArithmetic 15567 (1082471778575310291769/1000000000000000000000000) (74160059611447661453137/125000000000000000000000) (555191296573553/100000000000000000000000) where
  r0 := (8044751583/15625000000000000)
  k0 := (1696114137103043/500000000000000000)
  k6 := (2194967877977633/200000000000000000)
  q := (44112073177306006097/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15567]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15567]

theorem width_15568 : mW 15568 = 470776613202749 := by
  have hu : mW 15568 ≤ 470776613202749 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15568 ≤ 470776613202748 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15568 : RowArithmetic 15568 (135306216285858997651/125000000000000000000000) (593271257714008331867983/1000000000000000000000000) (5550987724946373/1000000000000000000000000) where
  r0 := (102962898837/200000000000000000)
  k0 := (212004053110529/62500000000000000)
  k6 := (342952715734923/31250000000000000)
  q := (176453960000902218347/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15568]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15568]

theorem width_15569 : mW 15569 = 470882461767146 := by
  have hu : mW 15569 ≤ 470882461767146 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15569 ≤ 470882461767145 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15569 : RowArithmetic 15569 (541213843362775838107/500000000000000000000000) (593262039696538708927483/1000000000000000000000000) (5550062699725013/1000000000000000000000000) where
  r0 := (32172805939/62500000000000000)
  k0 := (3391901443701807/1000000000000000000)
  k6 := (5487067225553929/500000000000000000)
  q := (88229813555283001063/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15569]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15569]

theorem width_15570 : mW 15570 = 470988327329595 := by
  have hu : mW 15570 ≤ 470988327329595 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15570 ≤ 470988327329594 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15570 : RowArithmetic 15570 (216481129578004371203/200000000000000000000000) (593252822838939156637123/1000000000000000000000000) (1109827578001389/200000000000000000000000) where
  r0 := (514715303827/1000000000000000000)
  k0 := (3391738056002181/1000000000000000000)
  k6 := (5486891016326839/500000000000000000)
  q := (44116323509558227919/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15570]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15570]

theorem width_15571 : mW 15571 = 471094209891732 := by
  have hu : mW 15571 ≤ 471094209891732 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15571 ≤ 471094209891731 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15571 : RowArithmetic 15571 (541191806889478211399/500000000000000000000000) (37077725446311017725331/62500000000000000000000) (5548213295727723/1000000000000000000000000) where
  r0 := (514665720591/1000000000000000000)
  k0 := (678314937332471/200000000000000000)
  k6 := (1371678706018693/125000000000000000)
  q := (88235480391960240067/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15571]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15571]

theorem width_15572 : mW 15572 = 471200109455196 := by
  have hu : mW 15572 ≤ 471200109455196 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15572 ≤ 471200109455195 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15572 : RowArithmetic 15572 (1082361584391028809449/1000000000000000000000000) (148308598150604234982877/250000000000000000000000) (5547288916822891/1000000000000000000000000) where
  r0 := (128654036329/250000000000000000)
  k0 := (3391411335684983/1000000000000000000)
  k6 := (5486538648795003/500000000000000000)
  q := (8823831367382311891/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15572]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15572]

theorem width_15573 : mW 15573 = 471306026021625 := by
  have hu : mW 15573 ≤ 471306026021625 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15573 ≤ 471306026021624 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15573 : RowArithmetic 15573 (270584889931228310201/250000000000000000000000) (74153147402878489771563/125000000000000000000000) (5546364753228027/1000000000000000000000000) where
  r0 := (514566577999/1000000000000000000)
  k0 := (3391248003062833/1000000000000000000)
  k6 := (5486362490484807/500000000000000000)
  q := (176482293729427712241/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15573]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15573]

theorem width_15574 : mW 15574 = 471411959592656 := by
  have hu : mW 15574 ≤ 471411959592656 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15574 ≤ 471411959592655 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15574 : RowArithmetic 15574 (541158769889642366423/500000000000000000000000) (5932159670025761419453/10000000000000000000000) (2772720402439373/500000000000000000000000) where
  r0 := (514517018639/1000000000000000000)
  k0 := (3391084688795261/1000000000000000000)
  k6 := (274309317457073/25000000000000000)
  q := (176487959929282428091/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15574]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15574]

theorem width_15575 : mW 15575 = 471517910169927 := by
  have hu : mW 15575 ≤ 471517910169927 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15575 ≤ 471517910169926 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15575 : RowArithmetic 15575 (1082295524552818462503/1000000000000000000000000) (593206755940828562718139/1000000000000000000000000) (1386129267927669/250000000000000000000000) where
  r0 := (514467467233/1000000000000000000)
  k0 := (3390921392875033/1000000000000000000)
  k6 := (5486010224762239/500000000000000000)
  q := (176493625947227907249/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15575]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15575]

theorem width_15576 : mW 15576 = 471623877755076 := by
  have hu : mW 15576 ≤ 471623877755076 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15576 ≤ 471623877755075 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15576 : RowArithmetic 15576 (1082273514044190082597/1000000000000000000000000) (593197546037552237903721/1000000000000000000000000) (5543593553659467/1000000000000000000000000) where
  r0 := (514417923781/1000000000000000000)
  k0 := (3390758115304799/1000000000000000000)
  k6 := (274291705867221/25000000000000000)
  q := (88249645891640834391/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15576]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15576]

theorem width_15577 : mW 15577 = 471729862349741 := by
  have hu : mW 15577 ≤ 471729862349741 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15577 ≤ 471729862349740 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15577 : RowArithmetic 15577 (1082251508252075721619/1000000000000000000000000) (296594168646257095476779/500000000000000000000000) (1108534050132159/200000000000000000000000) where
  r0 := (12859209707/25000000000000000)
  k0 := (3390594856077323/1000000000000000000)
  k6 := (2742829013442641/250000000000000000)
  q := (176504957437461228947/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15577]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15577]

theorem width_15578 : mW 15578 = 471835863955561 := by
  have hu : mW 15578 ≤ 471835863955561 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15578 ≤ 471835863955560 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15578 : RowArithmetic 15578 (1082229507175151669169/1000000000000000000000000) (593179129705481688241183/1000000000000000000000000) (1385436790662587/250000000000000000000000) where
  r0 := (64289857591/125000000000000000)
  k0 := (3390431615188663/1000000000000000000)
  k6 := (5485481953382103/500000000000000000)
  q := (176510622909784101187/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15578]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15578]

theorem width_15579 : mW 15579 = 471941882574173 := by
  have hu : mW 15579 ≤ 471941882574173 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15579 ≤ 471941882574172 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15579 : RowArithmetic 15579 (108220751081209531899/100000000000000000000000) (593169923276221863427951/1000000000000000000000000) (2770412144781931/500000000000000000000000) where
  r0 := (128567335281/250000000000000000)
  k0 := (339026839263817/100000000000000000)
  k6 := (10970611793664323/1000000000000000000)
  q := (176516288200267796137/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15579]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15579]

theorem width_15580 : mW 15580 = 472047918207215 := by
  have hu : mW 15580 ≤ 472047918207215 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15580 ≤ 472047918207214 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15580 : RowArithmetic 15580 (541092759580792112629/500000000000000000000000) (593160718004502032691229/1000000000000000000000000) (5539901631337083/1000000000000000000000000) where
  r0 := (257109914733/500000000000000000)
  k0 := (3390105188421903/1000000000000000000)
  k6 := (2742564928616369/250000000000000000)
  q := (8826097665446491081/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15580]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15580]

theorem width_15581 : mW 15581 = 472153970856327 := by
  have hu : mW 15581 ≤ 472153970856327 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15581 ≤ 472153970856326 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15581 : RowArithmetic 15581 (6763522076389348681/6250000000000000000000) (593151513890089557722087/1000000000000000000000000) (5538979187905761/1000000000000000000000000) where
  r0 := (64271290719/125000000000000000)
  k0 := (1694971001267957/500000000000000000)
  k6 := (685619229322639/62500000000000000)
  q := (44131904558946920663/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15581]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15581]

theorem width_15582 : mW 15582 = 472260040523145 := by
  have hu : mW 15582 ≤ 472260040523145 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15582 ≤ 472260040523144 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15582 : RowArithmetic 15582 (135267693749113642759/125000000000000000000000) (74142788866593975746663/125000000000000000000000) (2769028479602857/500000000000000000000000) where
  r0 := (25706041499/50000000000000000)
  k0 := (3389778834976259/1000000000000000000)
  k6 := (10969555657749129/1000000000000000000)
  q := (88266641490429440719/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15582]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15582]

theorem width_15583 : mW 15583 = 472366127209309 := by
  have hu : mW 15583 ≤ 472366127209309 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15583 ≤ 472366127209308 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15583 : RowArithmetic 15583 (1082119572472102634963/1000000000000000000000000) (118626621826451263410477/200000000000000000000000) (5537134945172739/1000000000000000000000000) where
  r0 := (514071342149/1000000000000000000)
  k0 := (3389615685742287/1000000000000000000)
  k6 := (5484601840110377/500000000000000000)
  q := (1379210527688757167/7812500000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15583]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15583]

theorem width_15584 : mW 15584 = 472472230916457 := by
  have hu : mW 15584 ≤ 472472230916457 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15584 ≤ 472472230916456 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15584 : RowArithmetic 15584 (1082097599658555720337/1000000000000000000000000) (29656195424418530710121/50000000000000000000000) (138405328643567/25000000000000000000000) where
  r0 := (514021862257/1000000000000000000)
  k0 := (67789051096601/20000000000000000)
  k6 := (10968851736571663/1000000000000000000)
  q := (11034038245356955441/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15584]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15584]

theorem width_15585 : mW 15585 = 472578351646227 := by
  have hu : mW 15585 ≤ 472578351646227 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15585 ≤ 472578351646226 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15585 : RowArithmetic 15585 (1082075631550948324809/1000000000000000000000000) (593114709000862314780929/1000000000000000000000000) (2767645780425703/500000000000000000000000) where
  r0 := (513972390301/1000000000000000000)
  k0 := (3389289442232303/1000000000000000000)
  k6 := (10968499826796421/1000000000000000000)
  q := (176550276125527484263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15585]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15585]

theorem width_15586 : mW 15586 = 472684489400258 := by
  have hu : mW 15586 ≤ 472684489400258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15586 ≤ 472684489400257 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15586 : RowArithmetic 15586 (1082053668147960535273/1000000000000000000000000) (593105510669499100716483/1000000000000000000000000) (1106874038086959/200000000000000000000000) where
  r0 := (513922926281/1000000000000000000)
  k0 := (3389126347951689/1000000000000000000)
  k6 := (2193629590177919/200000000000000000)
  q := (88277970071813499987/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15586]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15586]

theorem width_15587 : mW 15587 = 472790644180188 := by
  have hu : mW 15587 ≤ 472790644180188 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15587 ≤ 472790644180187 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15587 : RowArithmetic 15587 (216406341889654645169/200000000000000000000000) (593096313494048637589933/1000000000000000000000000) (1383362258607191/250000000000000000000000) where
  r0 := (256936735097/500000000000000000)
  k0 := (3388963271980961/1000000000000000000)
  k6 := (10967796108845753/1000000000000000000)
  q := (176561603980027322361/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15587]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15587]

theorem width_15588 : mW 15588 = 472896815987656 := by
  have hu : mW 15588 ≤ 472896815987656 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15588 ≤ 472896815987655 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15588 : RowArithmetic 15588 (1082009755450567430719/1000000000000000000000000) (296543558737139416165353/500000000000000000000000) (5532528092769241/1000000000000000000000000) where
  r0 := (513824022039/1000000000000000000)
  k0 := (677760042863893/200000000000000000)
  k6 := (1370930537582433/125000000000000000)
  q := (22070908454343242099/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15588]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15588]

theorem width_15589 : mW 15589 = 473003004824301 := by
  have hu : mW 15589 ≤ 473003004824301 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15589 ≤ 473003004824300 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15589 : RowArithmetic 15589 (67624237884595291099/62500000000000000000000) (118615584521991488573473/200000000000000000000000) (5531607365392179/1000000000000000000000000) where
  r0 := (256887290907/500000000000000000)
  k0 := (211789823435203/62500000000000000)
  k6 := (10967092526325297/1000000000000000000)
  q := (44143232776950081457/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15589]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15589]

theorem width_15590 : mW 15590 = 473109210691760 := by
  have hu : mW 15590 ≤ 473109210691760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15590 ≤ 473109210691759 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15590 : RowArithmetic 15590 (1081965861555827513273/1000000000000000000000000) (296534364450426234993119/500000000000000000000000) (5530686852233577/1000000000000000000000000) where
  r0 := (128431287379/250000000000000000)
  k0 := (3388474153905059/1000000000000000000)
  k6 := (438669631433513/40000000000000000)
  q := (176578594399207969231/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15590]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15590]

theorem width_15591 : mW 15591 = 473215433591674 := by
  have hu : mW 15591 ≤ 473215433591674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15591 ≤ 473215433591673 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15591 : RowArithmetic 15591 (1081943921656157825467/1000000000000000000000000) (593059536346731853832683/1000000000000000000000000) (1382441638307353/250000000000000000000000) where
  r0 := (102735145029/200000000000000000)
  k0 := (1694155575573769/500000000000000000)
  k6 := (10966389079191619/1000000000000000000)
  q := (44146064377246585989/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15591]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15591]

theorem width_15592 : mW 15592 = 473321673525681 := by
  have hu : mW 15592 ≤ 473321673525681 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15592 ≤ 473321673525680 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15592 : RowArithmetic 15592 (1081921986453198833723/1000000000000000000000000) (296525172473681868060797/500000000000000000000000) (5528846468315719/1000000000000000000000000) where
  r0 := (513626308699/1000000000000000000)
  k0 := (3388148166686731/1000000000000000000)
  k6 := (5483018703190627/500000000000000000)
  q := (44147480109288231039/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15592]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15592]

theorem width_15593 : mW 15593 = 473427930495420 := by
  have hu : mW 15593 ≤ 473427930495420 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15593 ≤ 473427930495419 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15593 : RowArithmetic 15593 (540950027972816968581/500000000000000000000000) (148260288675629040640769/250000000000000000000000) (1381981649357137/250000000000000000000000) where
  r0 := (20543076007/40000000000000000)
  k0 := (1693992600257691/500000000000000000)
  k6 := (2193137153480261/200000000000000000)
  q := (35319116636745036237/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15593]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15593]

theorem width_15594 : mW 15594 = 473534204502529 := by
  have hu : mW 15594 ≤ 473534204502529 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15594 ≤ 473534204502528 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15594 : RowArithmetic 15594 (1081878130132147319771/1000000000000000000000000) (593031965611957330341057/1000000000000000000000000) (276350347025199/50000000000000000000000) where
  r0 := (513527499573/1000000000000000000)
  k0 := (846955563159033/250000000000000000)
  k6 := (2741333540561587/250000000000000000)
  q := (88300622874360291797/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15594]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15594]

theorem width_15595 : mW 15595 = 473640495548648 := by
  have hu : mW 15595 ≤ 473640495548648 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15595 ≤ 473640495548647 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15595 : RowArithmetic 15595 (216371241802284602509/200000000000000000000000) (148255694418863873093399/250000000000000000000000) (5526087497478101/1000000000000000000000000) where
  r0 := (513478106889/1000000000000000000)
  k0 := (423457415379803/125000000000000000)
  k6 := (10964982590910961/1000000000000000000)
  q := (44151727033039149283/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15595]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15595]

theorem width_15596 : mW 15596 = 473746803635415 := by
  have hu : mW 15596 ≤ 473746803635415 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15596 ≤ 473746803635414 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15596 : RowArithmetic 15596 (67614643286384133961/62500000000000000000000) (593013590892778995535851/1000000000000000000000000) (5525168268287043/1000000000000000000000000) where
  r0 := (513428722123/1000000000000000000)
  k0 := (3387496411724897/1000000000000000000)
  k6 := (5482315526694861/500000000000000000)
  q := (11038285645878167797/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15596]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15596]

theorem width_15597 : mW 15597 = 473853128764470 := by
  have hu : mW 15597 ≤ 473853128764470 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15597 ≤ 473853128764469 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15597 : RowArithmetic 15597 (1081812380843001687191/1000000000000000000000000) (118600881052739229628779/200000000000000000000000) (690531156608367/125000000000000000000000) where
  r0 := (64172418159/125000000000000000)
  k0 := (846833379672073/250000000000000000)
  k6 := (10964279549677211/1000000000000000000)
  q := (44154558088605076651/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15597]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15597]

theorem width_15598 : mW 15598 = 473959470937452 := by
  have hu : mW 15598 ≤ 473959470937452 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15598 ≤ 473959470937451 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15598 : RowArithmetic 15598 (1081790473792675402909/1000000000000000000000000) (296497610393987728563161/500000000000000000000000) (110466609023079/20000000000000000000000) where
  r0 := (102665995267/200000000000000000)
  k0 := (1693585321963973/500000000000000000)
  k6 := (1096392807976801/100000000000000000)
  q := (176623894193282920041/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15598]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15598]

theorem width_15599 : mW 15599 = 474065830156000 := by
  have hu : mW 15599 ≤ 474065830156000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15599 ≤ 474065830155999 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15599 : RowArithmetic 15599 (1081768571429853520751/1000000000000000000000000) (148246509366346346213387/250000000000000000000000) (2761205931542137/500000000000000000000000) where
  r0 := (513280615311/1000000000000000000)
  k0 := (846751946860799/250000000000000000)
  k6 := (109635766436567/10000000000000000)
  q := (176629555850655979619/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15599]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15599]

theorem width_15600 : mW 15600 = 474172206421754 := by
  have hu : mW 15600 ≤ 474172206421754 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15600 ≤ 474172206421753 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15600 : RowArithmetic 15600 (270436668438305607563/250000000000000000000000) (296488427647847256370517/500000000000000000000000) (2760746744297057/500000000000000000000000) where
  r0 := (128307815549/250000000000000000)
  k0 := (3386844949223481/1000000000000000000)
  k6 := (5481612620668933/500000000000000000)
  q := (22079402165819617137/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15600]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15600]

theorem width_15601 : mW 15601 = 474278599736351 := by
  have hu : mW 15601 ≤ 474278599736351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15601 ≤ 474278599736350 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15601 : RowArithmetic 15601 (1081724780761469927241/1000000000000000000000000) (592967674278671463141597/1000000000000000000000000) (5520575327619731/1000000000000000000000000) where
  r0 := (51318191699/100000000000000000)
  k0 := (677336425854287/200000000000000000)
  k6 := (10962873872806091/1000000000000000000)
  q := (176640878621003241431/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15601]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15601]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15527 then ⟨(67709850102597984067/62500000000000000000000), (296825098983093709162089/500000000000000000000000), (5589100106148017/1000000000000000000000000)⟩ else
  if n = 15528 then ⟨(1083335363174888101811/1000000000000000000000000), (593640932192383779496103/1000000000000000000000000), (5588166189494173/1000000000000000000000000)⟩ else
  if n = 15529 then ⟨(1083313129488790236979/1000000000000000000000000), (37101979224254429660103/62500000000000000000000), (1117446498201429/200000000000000000000000)⟩ else
  if n = 15530 then ⟨(1083290900581927702163/1000000000000000000000000), (593622404153012831539999/1000000000000000000000000), (1117259802124293/200000000000000000000000)⟩ else
  if n = 15531 then ⟨(6770429227830973841/6250000000000000000000), (148403285471743429224589/250000000000000000000000), (698170718533967/125000000000000000000000)⟩ else
  if n = 15532 then ⟨(5416232285502647079/5000000000000000000000), (296801940394858843601973/500000000000000000000000), (111688654077851/20000000000000000000000)⟩ else
  if n = 15533 then ⟨(1083224242523304791559/1000000000000000000000000), (74199327607626132297739/125000000000000000000000), (2791749938709279/500000000000000000000000)⟩ else
  if n = 15534 then ⟨(270800508179984438053/250000000000000000000000), (593585362100612099450919/1000000000000000000000000), (5582567268784403/1000000000000000000000000)⟩ else
  if n = 15535 then ⟨(541589913844542615789/500000000000000000000000), (118715220901658231260699/200000000000000000000000), (2790817438962387/500000000000000000000000)⟩ else
  if n = 15536 then ⟨(270789406857351002059/250000000000000000000000), (4748534784670485507799/8000000000000000000000), (139517567619359/25000000000000000000000)⟩ else
  if n = 15537 then ⟨(1083135431939551983279/1000000000000000000000000), (296778796413467597019253/500000000000000000000000), (5579770749267901/1000000000000000000000000)⟩ else
  if n = 15538 then ⟨(216622648243637444333/200000000000000000000000), (593548338737429247851251/1000000000000000000000000), (1394709752835037/250000000000000000000000)⟩ else
  if n = 15539 then ⟨(216618211052793654309/200000000000000000000000), (593539085815057511901407/1000000000000000000000000), (1394476872731469/250000000000000000000000)⟩ else
  if n = 15540 then ⟨(541534437037776922601/500000000000000000000000), (74191229257448078840697/125000000000000000000000), (5576976187959873/1000000000000000000000000)⟩ else
  if n = 15541 then ⟨(1083046697651603775577/1000000000000000000000000), (11870411669415507308267/20000000000000000000000), (348502818898561/62500000000000000000000)⟩ else
  if n = 15542 then ⟨(135378065748847217557/125000000000000000000000), (296755667024197293102471/500000000000000000000000), (5575114234112023/1000000000000000000000000)⟩ else
  if n = 15543 then ⟨(270750589772934054719/250000000000000000000000), (593502085792207163551331/1000000000000000000000000), (2787091791549943/500000000000000000000000)⟩ else
  if n = 15544 then ⟨(216596039390628034389/200000000000000000000000), (23739713548079121846679/40000000000000000000000), (696656643659433/125000000000000000000000)⟩ else
  if n = 15545 then ⟨(135369754946706380327/125000000000000000000000), (74185449097184038507591/125000000000000000000000), (69654036657171/12500000000000000000000)⟩ else
  if n = 15546 then ⟨(541467943475965059611/500000000000000000000000), (593474348018454989553573/1000000000000000000000000), (348212058308091/62500000000000000000000)⟩ else
  if n = 15547 then ⟨(135364217385830055557/125000000000000000000000), (74183138053086405201237/125000000000000000000000), (1392615787569447/250000000000000000000000)⟩ else
  if n = 15548 then ⟨(541445797988221975907/500000000000000000000000), (118691172399189260726903/200000000000000000000000), (1113906716910727/200000000000000000000000)⟩ else
  if n = 15549 then ⟨(1082869457620004328231/1000000000000000000000000), (593446620731985466805109/1000000000000000000000000), (556860423569203/100000000000000000000000)⟩ else
  if n = 15550 then ⟨(1082847324015985105597/1000000000000000000000000), (593437380632574065034991/1000000000000000000000000), (2783837551814003/500000000000000000000000)⟩ else
  if n = 15551 then ⟨(135353149395381326789/125000000000000000000000), (593428141697477504601627/1000000000000000000000000), (556674618829663/100000000000000000000000)⟩ else
  if n = 15552 then ⟨(1082803071059865030233/1000000000000000000000000), (296709451963230641595991/500000000000000000000000), (5565817489632973/1000000000000000000000000)⟩ else
  if n = 15553 then ⟨(1082780951705093644807/1000000000000000000000000), (593409667319290941253969/1000000000000000000000000), (5564889007572153/1000000000000000000000000)⟩ else
  if n = 15554 then ⟨(54137941854870095607/50000000000000000000000), (593400431875732047356041/1000000000000000000000000), (5563960742049299/1000000000000000000000000)⟩ else
  if n = 15555 then ⟨(1082736727235455766421/1000000000000000000000000), (593391197595550349835541/1000000000000000000000000), (2781516346499783/500000000000000000000000)⟩ else
  if n = 15556 then ⟨(541357311058960969319/500000000000000000000000), (148345491119627872385297/250000000000000000000000), (1112420972071629/200000000000000000000000)⟩ else
  if n = 15557 then ⟨(1082692521743466688491/1000000000000000000000000), (296686366262190695858227/500000000000000000000000), (1112235448812043/200000000000000000000000)⟩ else
  if n = 15558 then ⟨(1082670426110758022833/1000000000000000000000000), (296681750866462906828963/500000000000000000000000), (2780124922020513/500000000000000000000000)⟩ else
  if n = 15559 then ⟨(216529667043692758721/200000000000000000000000), (593354272103910760262703/1000000000000000000000000), (694915332529479/125000000000000000000000)⟩ else
  if n = 15560 then ⟨(541313124532625849397/500000000000000000000000), (37084065227318886735957/62500000000000000000000), (5558395692579883/1000000000000000000000000)⟩ else
  if n = 15561 then ⟨(1082604167649790865107/1000000000000000000000000), (593335816332266129068597/1000000000000000000000000), (5557468941008493/1000000000000000000000000)⟩ else
  if n = 15562 then ⟨(27064552274268764527/25000000000000000000000), (593326590189168808563559/1000000000000000000000000), (1111308481091397/200000000000000000000000)⟩ else
  if n = 15563 then ⟨(6766000118917501859/6250000000000000000000), (148329341301894088355417/250000000000000000000000), (5555616085860697/1000000000000000000000000)⟩ else
  if n = 15564 then ⟨(541268975908305287723/500000000000000000000000), (74163517673406872032723/125000000000000000000000), (2777344991077507/500000000000000000000000)⟩ else
  if n = 15565 then ⟨(108251588933885150613/100000000000000000000000), (74162364840996389012201/125000000000000000000000), (1388441023568827/250000000000000000000000)⟩ else
  if n = 15566 then ⟨(541246915796097145303/500000000000000000000000), (148322424307372767322577/250000000000000000000000), (2776419211078501/500000000000000000000000)⟩ else
  if n = 15567 then ⟨(1082471778575310291769/1000000000000000000000000), (74160059611447661453137/125000000000000000000000), (555191296573553/100000000000000000000000)⟩ else
  if n = 15568 then ⟨(135306216285858997651/125000000000000000000000), (593271257714008331867983/1000000000000000000000000), (5550987724946373/1000000000000000000000000)⟩ else
  if n = 15569 then ⟨(541213843362775838107/500000000000000000000000), (593262039696538708927483/1000000000000000000000000), (5550062699725013/1000000000000000000000000)⟩ else
  if n = 15570 then ⟨(216481129578004371203/200000000000000000000000), (593252822838939156637123/1000000000000000000000000), (1109827578001389/200000000000000000000000)⟩ else
  if n = 15571 then ⟨(541191806889478211399/500000000000000000000000), (37077725446311017725331/62500000000000000000000), (5548213295727723/1000000000000000000000000)⟩ else
  if n = 15572 then ⟨(1082361584391028809449/1000000000000000000000000), (148308598150604234982877/250000000000000000000000), (5547288916822891/1000000000000000000000000)⟩ else
  if n = 15573 then ⟨(270584889931228310201/250000000000000000000000), (74153147402878489771563/125000000000000000000000), (5546364753228027/1000000000000000000000000)⟩ else
  if n = 15574 then ⟨(541158769889642366423/500000000000000000000000), (5932159670025761419453/10000000000000000000000), (2772720402439373/500000000000000000000000)⟩ else
  if n = 15575 then ⟨(1082295524552818462503/1000000000000000000000000), (593206755940828562718139/1000000000000000000000000), (1386129267927669/250000000000000000000000)⟩ else
  if n = 15576 then ⟨(1082273514044190082597/1000000000000000000000000), (593197546037552237903721/1000000000000000000000000), (5543593553659467/1000000000000000000000000)⟩ else
  if n = 15577 then ⟨(1082251508252075721619/1000000000000000000000000), (296594168646257095476779/500000000000000000000000), (1108534050132159/200000000000000000000000)⟩ else
  if n = 15578 then ⟨(1082229507175151669169/1000000000000000000000000), (593179129705481688241183/1000000000000000000000000), (1385436790662587/250000000000000000000000)⟩ else
  if n = 15579 then ⟨(108220751081209531899/100000000000000000000000), (593169923276221863427951/1000000000000000000000000), (2770412144781931/500000000000000000000000)⟩ else
  if n = 15580 then ⟨(541092759580792112629/500000000000000000000000), (593160718004502032691229/1000000000000000000000000), (5539901631337083/1000000000000000000000000)⟩ else
  if n = 15581 then ⟨(6763522076389348681/6250000000000000000000), (593151513890089557722087/1000000000000000000000000), (5538979187905761/1000000000000000000000000)⟩ else
  if n = 15582 then ⟨(135267693749113642759/125000000000000000000000), (74142788866593975746663/125000000000000000000000), (2769028479602857/500000000000000000000000)⟩ else
  if n = 15583 then ⟨(1082119572472102634963/1000000000000000000000000), (118626621826451263410477/200000000000000000000000), (5537134945172739/1000000000000000000000000)⟩ else
  if n = 15584 then ⟨(1082097599658555720337/1000000000000000000000000), (29656195424418530710121/50000000000000000000000), (138405328643567/25000000000000000000000)⟩ else
  if n = 15585 then ⟨(1082075631550948324809/1000000000000000000000000), (593114709000862314780929/1000000000000000000000000), (2767645780425703/500000000000000000000000)⟩ else
  if n = 15586 then ⟨(1082053668147960535273/1000000000000000000000000), (593105510669499100716483/1000000000000000000000000), (1106874038086959/200000000000000000000000)⟩ else
  if n = 15587 then ⟨(216406341889654645169/200000000000000000000000), (593096313494048637589933/1000000000000000000000000), (1383362258607191/250000000000000000000000)⟩ else
  if n = 15588 then ⟨(1082009755450567430719/1000000000000000000000000), (296543558737139416165353/500000000000000000000000), (5532528092769241/1000000000000000000000000)⟩ else
  if n = 15589 then ⟨(67624237884595291099/62500000000000000000000), (118615584521991488573473/200000000000000000000000), (5531607365392179/1000000000000000000000000)⟩ else
  if n = 15590 then ⟨(1081965861555827513273/1000000000000000000000000), (296534364450426234993119/500000000000000000000000), (5530686852233577/1000000000000000000000000)⟩ else
  if n = 15591 then ⟨(1081943921656157825467/1000000000000000000000000), (593059536346731853832683/1000000000000000000000000), (1382441638307353/250000000000000000000000)⟩ else
  if n = 15592 then ⟨(1081921986453198833723/1000000000000000000000000), (296525172473681868060797/500000000000000000000000), (5528846468315719/1000000000000000000000000)⟩ else
  if n = 15593 then ⟨(540950027972816968581/500000000000000000000000), (148260288675629040640769/250000000000000000000000), (1381981649357137/250000000000000000000000)⟩ else
  if n = 15594 then ⟨(1081878130132147319771/1000000000000000000000000), (593031965611957330341057/1000000000000000000000000), (276350347025199/50000000000000000000000)⟩ else
  if n = 15595 then ⟨(216371241802284602509/200000000000000000000000), (148255694418863873093399/250000000000000000000000), (5526087497478101/1000000000000000000000000)⟩ else
  if n = 15596 then ⟨(67614643286384133961/62500000000000000000000), (593013590892778995535851/1000000000000000000000000), (5525168268287043/1000000000000000000000000)⟩ else
  if n = 15597 then ⟨(1081812380843001687191/1000000000000000000000000), (118600881052739229628779/200000000000000000000000), (690531156608367/125000000000000000000000)⟩ else
  if n = 15598 then ⟨(1081790473792675402909/1000000000000000000000000), (296497610393987728563161/500000000000000000000000), (110466609023079/20000000000000000000000)⟩ else
  if n = 15599 then ⟨(1081768571429853520751/1000000000000000000000000), (148246509366346346213387/250000000000000000000000), (2761205931542137/500000000000000000000000)⟩ else
  if n = 15600 then ⟨(270436668438305607563/250000000000000000000000), (296488427647847256370517/500000000000000000000000), (2760746744297057/500000000000000000000000)⟩ else
  ⟨(1081724780761469927241/1000000000000000000000000), (592967674278671463141597/1000000000000000000000000), (5520575327619731/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15527 ≤ n) (hb : n ≤ 15601) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15527
  · exact row_15528
  · exact row_15529
  · exact row_15530
  · exact row_15531
  · exact row_15532
  · exact row_15533
  · exact row_15534
  · exact row_15535
  · exact row_15536
  · exact row_15537
  · exact row_15538
  · exact row_15539
  · exact row_15540
  · exact row_15541
  · exact row_15542
  · exact row_15543
  · exact row_15544
  · exact row_15545
  · exact row_15546
  · exact row_15547
  · exact row_15548
  · exact row_15549
  · exact row_15550
  · exact row_15551
  · exact row_15552
  · exact row_15553
  · exact row_15554
  · exact row_15555
  · exact row_15556
  · exact row_15557
  · exact row_15558
  · exact row_15559
  · exact row_15560
  · exact row_15561
  · exact row_15562
  · exact row_15563
  · exact row_15564
  · exact row_15565
  · exact row_15566
  · exact row_15567
  · exact row_15568
  · exact row_15569
  · exact row_15570
  · exact row_15571
  · exact row_15572
  · exact row_15573
  · exact row_15574
  · exact row_15575
  · exact row_15576
  · exact row_15577
  · exact row_15578
  · exact row_15579
  · exact row_15580
  · exact row_15581
  · exact row_15582
  · exact row_15583
  · exact row_15584
  · exact row_15585
  · exact row_15586
  · exact row_15587
  · exact row_15588
  · exact row_15589
  · exact row_15590
  · exact row_15591
  · exact row_15592
  · exact row_15593
  · exact row_15594
  · exact row_15595
  · exact row_15596
  · exact row_15597
  · exact row_15598
  · exact row_15599
  · exact row_15600
  · exact row_15601

end BstLean.Part271.R3.Rows15527
