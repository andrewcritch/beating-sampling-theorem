import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15701–15775. -/
namespace BstLean.Part271.R3.Rows15701
open Real BstLean.Part130 BstLean.Part227

theorem width_15701 : mW 15701 = 485004309558570 := by
  have hu : mW 15701 ≤ 485004309558570 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15701 ≤ 485004309558569 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15701 : RowArithmetic 15701 (134944864598205489963/125000000000000000000000) (592055354103056416755951/1000000000000000000000000) (5429826638348373/1000000000000000000000000) where
  r0 := (254143515987/500000000000000000)
  k0 := (421311478537163/125000000000000000)
  k6 := (1365988339979123/125000000000000000)
  q := (44301523675828577533/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15701]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15701]

theorem width_15702 : mW 15702 = 485112433259711 := by
  have hu : mW 15702 ≤ 485112433259711 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15702 ≤ 485112433259710 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15702 : RowArithmetic 15702 (1079537490283289148989/1000000000000000000000000) (592046288324889129418411/1000000000000000000000000) (2714464859041443/500000000000000000000000) where
  r0 := (254119238239/500000000000000000)
  k0 := (3370330836770079/1000000000000000000)
  k6 := (341486210503559/31250000000000000)
  q := (177211737760228512467/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15702]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15702]

theorem width_15703 : mW 15703 = 485220574177181 := by
  have hu : mW 15703 ≤ 485220574177181 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15703 ≤ 485220574177180 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15703 : RowArithmetic 15703 (269879017083562199919/250000000000000000000000) (592037223676121303844031/1000000000000000000000000) (542803300494953/100000000000000000000000) where
  r0 := (508189928711/1000000000000000000)
  k0 := (421271232897577/125000000000000000)
  k6 := (10927210785635823/1000000000000000000)
  q := (35443476127490655597/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15703]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15703]

theorem width_15704 : mW 15704 = 485328732312622 := by
  have hu : mW 15704 ≤ 485328732312622 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15704 ≤ 485328732312621 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15704 : RowArithmetic 15704 (8433551960447317177/7812500000000000000000) (74003520019566002219059/125000000000000000000000) (21199751948777/3906250000000000000000) where
  r0 := (508141388673/1000000000000000000)
  k0 := (674001781506297/200000000000000000)
  k6 := (2185372573678699/200000000000000000)
  q := (35444604667001154183/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15704]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15704]

theorem width_15705 : mW 15705 = 485436907667680 := by
  have hu : mW 15705 ≤ 485436907667680 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15705 ≤ 485436907667679 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15705 : RowArithmetic 15705 (1079473238091045523553/1000000000000000000000000) (118403819553176879566069/200000000000000000000000) (5426240199833619/1000000000000000000000000) where
  r0 := (254046428181/500000000000000000)
  k0 := (1645433579013/488281250000000)
  k6 := (2185302996876323/200000000000000000)
  q := (177228665852903152751/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15705]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15705]

theorem width_15706 : mW 15706 = 485545100243999 := by
  have hu : mW 15706 ≤ 485545100243999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15706 ≤ 485545100243998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15706 : RowArithmetic 15706 (1079451829794349603121/1000000000000000000000000) (148002509125991407867553/250000000000000000000000) (2712672053864141/500000000000000000000000) where
  r0 := (20321773271/40000000000000000)
  k0 := (673937410006931/200000000000000000)
  k6 := (2731541783398723/250000000000000000)
  q := (177234308191162582257/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15706]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15706]

theorem width_15707 : mW 15707 = 485653310043225 := by
  have hu : mW 15707 ≤ 485653310043225 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15707 ≤ 485653310043224 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15707 : RowArithmetic 15707 (134928803255737839681/125000000000000000000000) (296000488185273503250611/500000000000000000000000) (1356112055627383/250000000000000000000000) where
  r0 := (496089663/976562500000000)
  k0 := (673905229636429/200000000000000000)
  k6 := (5462909658014019/500000000000000000)
  q := (35447990069960243093/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15707]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15707]

theorem width_15708 : mW 15708 = 485761537067003 := by
  have hu : mW 15708 ≤ 485761537067003 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15708 ≤ 485761537067002 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15708 : RowArithmetic 15708 (539704513422219748691/500000000000000000000000) (591991917365403887675703/1000000000000000000000000) (1084710508823207/200000000000000000000000) where
  r0 := (507947305771/1000000000000000000)
  k0 := (3369365264257031/1000000000000000000)
  k6 := (5462735765837883/500000000000000000)
  q := (44311398082209051419/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15708]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15708]

theorem width_15709 : mW 15709 = 485869781316976 := by
  have hu : mW 15709 ≤ 485869781316976 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15709 ≤ 485869781316975 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15709 : RowArithmetic 15709 (1079387632188695623169/1000000000000000000000000) (295991429744155813372047/500000000000000000000000) (2711328536243251/500000000000000000000000) where
  r0 := (507898804349/1000000000000000000)
  k0 := (3369204398251931/1000000000000000000)
  k6 := (1092512378053279/100000000000000000)
  q := (177251234128284703461/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15709]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15709]

theorem width_15710 : mW 15710 = 485978042794791 := by
  have hu : mW 15710 ≤ 485978042794791 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15710 ≤ 485978042794790 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15710 : RowArithmetic 15710 (1079366242077406027413/1000000000000000000000000) (73996725342380710415099/125000000000000000000000) (2710880903779811/500000000000000000000000) where
  r0 := (253925155323/500000000000000000)
  k0 := (336904355016941/100000000000000000)
  k6 := (5462388031296913/500000000000000000)
  q := (22157109468520482083/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15710]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15710]

theorem width_15711 : mW 15711 = 486086321502093 := by
  have hu : mW 15711 ≤ 486086321502093 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15711 ≤ 486086321502092 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15711 : RowArithmetic 15711 (215868971301861338429/200000000000000000000000) (295982373558690805757921/500000000000000000000000) (338804171829633/62500000000000000000000) where
  r0 := (253900912329/500000000000000000)
  k0 := (3368882719998769/1000000000000000000)
  k6 := (10924428377853589/1000000000000000000)
  q := (177262517188490810397/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15711]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15711]

theorem width_15712 : mW 15712 = 486194617440526 := by
  have hu : mW 15712 ≤ 486194617440526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15712 ≤ 486194617440525 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15712 : RowArithmetic 15712 (1079323475483134348439/1000000000000000000000000) (591955692623094956864037/1000000000000000000000000) (1354992974392197/250000000000000000000000) where
  r0 := (253876673193/500000000000000000)
  k0 := (3368721907745889/1000000000000000000)
  k6 := (10924080726306797/1000000000000000000)
  q := (35453631689856541409/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15712]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15712]

theorem width_15713 : mW 15713 = 486302930611735 := by
  have hu : mW 15713 ≤ 486302930611735 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15713 ≤ 486302930611734 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15713 : RowArithmetic 15713 (539651049498812938873/500000000000000000000000) (591946639255961347697223/1000000000000000000000000) (5419077252382383/1000000000000000000000000) where
  r0 := (253852437913/500000000000000000)
  k0 := (842140278350017/250000000000000000)
  k6 := (1365466638493521/125000000000000000)
  q := (177273799530556686267/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15713]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15713]

theorem width_15714 : mW 15714 = 486411261017366 := by
  have hu : mW 15714 ≤ 486411261017366 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15714 ≤ 486411261017365 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15714 : RowArithmetic 15714 (269820181762879578059/250000000000000000000000) (591937587015756533282191/1000000000000000000000000) (2709091406826851/500000000000000000000000) where
  r0 := (253828206489/500000000000000000)
  k0 := (3368400336963869/1000000000000000000)
  k6 := (1365423190346553/125000000000000000)
  q := (2769991256755154453/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15714]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15714]

theorem width_15715 : mW 15715 = 486519608659065 := by
  have hu : mW 15715 ≤ 486519608659065 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15715 ≤ 486519608659064 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15715 : RowArithmetic 15715 (1079259359643549133881/1000000000000000000000000) (36995533493891012494009/62500000000000000000000) (5417288581321559/1000000000000000000000000) where
  r0 := (507607957839/1000000000000000000)
  k0 := (3368239578429903/1000000000000000000)
  k6 := (2730759492693571/250000000000000000)
  q := (7091403246184777497/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15715]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15715]

theorem width_15716 : mW 15716 = 486627973538476 := by
  have hu : mW 15716 ≤ 486627973538476 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15716 ≤ 486627973538475 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15716 : RowArithmetic 15716 (1079237996772456871491/1000000000000000000000000) (59191948591523623436411/100000000000000000000000) (5416394555324813/1000000000000000000000000) where
  r0 := (63444938801/125000000000000000)
  k0 := (1684039418898709/500000000000000000)
  k6 := (10922690451948471/1000000000000000000)
  q := (88645360848721237523/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15716]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15716]

theorem width_15717 : mW 15717 = 486736355657244 := by
  have hu : mW 15717 ≤ 486736355657244 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15717 ≤ 486736355657243 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15717 : RowArithmetic 15717 (1079216638436980203869/1000000000000000000000000) (295955218527236254439349/500000000000000000000000) (1083100147120467/200000000000000000000000) where
  r0 := (126877767671/250000000000000000)
  k0 := (420989764383207/125000000000000000)
  k6 := (2730585741572427/250000000000000000)
  q := (88648181030408063303/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15717]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15717]

theorem width_15718 : mW 15718 = 486844755017016 := by
  have hu : mW 15718 ≤ 486844755017016 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15718 ≤ 486844755017015 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15718 : RowArithmetic 15718 (4316781138543430647/4000000000000000000000) (73987673664967621757861/125000000000000000000000) (1082921424418599/200000000000000000000000) where
  r0 := (507462638663/1000000000000000000)
  k0 := (3367757410223909/1000000000000000000)
  k6 := (10921995513792721/1000000000000000000)
  q := (22162750280594689767/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15718]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15718]

theorem width_15719 : mW 15719 = 486953171619437 := by
  have hu : mW 15719 ≤ 486953171619437 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15719 ≤ 486953171619436 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15719 : RowArithmetic 15719 (1079173935367828821869/1000000000000000000000000) (591892342710817592496801/1000000000000000000000000) (1353428428683927/250000000000000000000000) where
  r0 := (101482842869/200000000000000000)
  k0 := (1683798361637369/500000000000000000)
  k6 := (5460824047226117/500000000000000000)
  q := (177307642249283772941/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15719]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15719]

theorem width_15720 : mW 15720 = 487061605466152 := by
  have hu : mW 15720 ≤ 487061605466152 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15720 ≤ 487061605466151 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15720 : RowArithmetic 15720 (269788147657908427321/250000000000000000000000) (591883297227478475697347/1000000000000000000000000) (2706410256734707/500000000000000000000000) where
  r0 := (15855181179/31250000000000000)
  k0 := (3367436054214067/1000000000000000000)
  k6 := (436852028330519/40000000000000000)
  q := (88656641037206005801/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15720]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15720]

theorem width_15721 : mW 15721 = 487170056558806 := by
  have hu : mW 15721 ≤ 487170056558806 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15721 ≤ 487170056558805 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15721 : RowArithmetic 15721 (134891406303251599647/125000000000000000000000) (591874252869499736867081/1000000000000000000000000) (338245469889567/62500000000000000000000) where
  r0 := (507317388811/1000000000000000000)
  k0 := (3367275403041137/1000000000000000000)
  k6 := (10920953355219671/1000000000000000000)
  q := (88659460860079675989/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15721]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15721]

theorem width_15722 : mW 15722 = 487278524899046 := by
  have hu : mW 15722 ≤ 487278524899046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15722 ≤ 487278524899045 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15722 : RowArithmetic 15722 (539554957374853205357/500000000000000000000000) (295932604818328788903601/500000000000000000000000) (1082206945793129/200000000000000000000000) where
  r0 := (507268987591/1000000000000000000)
  k0 := (3367114769748553/1000000000000000000)
  k6 := (10920606035317053/1000000000000000000)
  q := (88662280593271454603/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15722]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15722]

theorem width_15723 : mW 15723 = 487387010488517 := by
  have hu : mW 15723 ≤ 487387010488517 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15723 ≤ 487387010488516 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15723 : RowArithmetic 15723 (539544291800727959679/500000000000000000000000) (295928083764364104640643/500000000000000000000000) (5410142145606139/1000000000000000000000000) where
  r0 := (253610297033/500000000000000000)
  k0 := (841738538583059/250000000000000000)
  k6 := (218405174970997/20000000000000000)
  q := (177330200473579795703/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15723]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15723]

theorem width_15724 : mW 15724 = 487495513328865 := by
  have hu : mW 15724 ≤ 487495513328865 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15724 ≤ 487495513328864 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15724 : RowArithmetic 15724 (1079067256980002842331/1000000000000000000000000) (591847126545488030788499/1000000000000000000000000) (5409249768093571/1000000000000000000000000) where
  r0 := (126793052059/250000000000000000)
  k0 := (420849194599343/125000000000000000)
  k6 := (5459955747456397/500000000000000000)
  q := (88667919790643560581/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15724]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15724]

theorem width_15725 : mW 15725 = 487604033421736 := by
  have hu : mW 15725 ≤ 487604033421736 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15725 ≤ 487604033421735 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15725 : RowArithmetic 15725 (1079045934884089146587/1000000000000000000000000) (59183808668671336098459/100000000000000000000000) (2704178798183491/500000000000000000000000) where
  r0 := (253561915049/500000000000000000)
  k0 := (1683316488564339/500000000000000000)
  k6 := (10919564274400619/1000000000000000000)
  q := (88670739254840996279/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15725]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15725]

theorem width_15726 : mW 15726 = 487712570768775 := by
  have hu : mW 15726 ≤ 487712570768775 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15726 ≤ 487712570768774 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15726 : RowArithmetic 15726 (215804923462491508827/200000000000000000000000) (295914523976090315310119/500000000000000000000000) (2703732815182723/500000000000000000000000) where
  r0 := (507075459651/1000000000000000000)
  k0 := (134658896613331/40000000000000000)
  k6 := (10919217087008057/1000000000000000000)
  q := (88673558629390757073/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15726]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15726]

theorem width_15727 : mW 15727 = 487821125371628 := by
  have hu : mW 15727 ≤ 487821125371628 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15727 ≤ 487821125371627 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15727 : RowArithmetic 15727 (215800660852770179291/200000000000000000000000) (7397750129270828861003/12500000000000000000000) (5406573870028049/1000000000000000000000000) where
  r0 := (507027096893/1000000000000000000)
  k0 := (3366311871404453/1000000000000000000)
  k6 := (2729717483182461/250000000000000000)
  q := (8867637791430139373/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15727]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15727]

theorem width_15728 : mW 15728 = 487929697231942 := by
  have hu : mW 15728 ≤ 487929697231942 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15728 ≤ 487929697231941 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15728 : RowArithmetic 15728 (215796399147402442969/200000000000000000000000) (295905486927473504749527/500000000000000000000000) (84463786176467/15625000000000000000000) where
  r0 := (253489370911/500000000000000000)
  k0 := (336615134533813/100000000000000000)
  k6 := (2729630702890179/250000000000000000)
  q := (4433959855479072783/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15728]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15728]

theorem width_15729 : mW 15729 = 488038286351362 := by
  have hu : mW 15729 ≤ 488038286351362 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15729 ≤ 488038286351361 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15729 : RowArithmetic 15729 (539480345865342776169/500000000000000000000000) (591801938491799338857569/1000000000000000000000000) (1080958193220421/200000000000000000000000) where
  r0 := (506930394437/1000000000000000000)
  k0 := (3365990837133541/1000000000000000000)
  k6 := (2729543930873853/250000000000000000)
  q := (177364032430478981823/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15729]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15729]

theorem width_15730 : mW 15730 = 488146892731534 := by
  have hu : mW 15730 ≤ 488146892731534 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15730 ≤ 488146892731533 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15730 : RowArithmetic 15730 (67433712015225944447/62500000000000000000000) (591792904251999968413979/1000000000000000000000000) (5403899822391853/1000000000000000000000000) where
  r0 := (101376410947/200000000000000000)
  k0 := (42072879334791/12500000000000000)
  k6 := (10917828668528669/1000000000000000000)
  q := (177369670462568092353/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15730]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15730]

theorem width_15731 : mW 15731 = 488255516374105 := by
  have hu : mW 15731 ≤ 488255516374105 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15731 ≤ 488255516374104 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15731 : RowArithmetic 15731 (1078918097274545243039/1000000000000000000000000) (591783871135325627096911/1000000000000000000000000) (675376110512787/125000000000000000000000) where
  r0 := (101366744543/200000000000000000)
  k0 := (1682834937143291/500000000000000000)
  k6 := (10917481646655227/1000000000000000000)
  q := (177375308315447333573/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15731]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15731]

theorem width_15732 : mW 15732 = 488364157280721 := by
  have hu : mW 15732 ≤ 488364157280721 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15732 ≤ 488364157280720 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15732 : RowArithmetic 15732 (215779361364444208669/200000000000000000000000) (591774839141553117607857/1000000000000000000000000) (1080423630234527/200000000000000000000000) where
  r0 := (63348174797/125000000000000000)
  k0 := (3365509419642679/1000000000000000000)
  k6 := (2729283664467457/250000000000000000)
  q := (35476189197826758687/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15732]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15732]

theorem width_15733 : mW 15733 = 488472815453027 := by
  have hu : mW 15733 ≤ 488472815453027 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15733 ≤ 488472815453026 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15733 : RowArithmetic 15733 (1078875520885388350261/1000000000000000000000000) (29588290413522966115701/50000000000000000000000) (5401227623542101/1000000000000000000000000) where
  r0 := (126684270429/250000000000000000)
  k0 := (673069796569497/200000000000000000)
  k6 := (10916787702167213/1000000000000000000)
  q := (177386583483644557171/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15733]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15733]

theorem width_15734 : mW 15734 = 488581490892671 := by
  have hu : mW 15734 ≤ 488581490892671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15734 ≤ 488581490892670 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15734 : RowArithmetic 15734 (539427119731396278749/500000000000000000000000) (591756778521821161928393/1000000000000000000000000) (2700168650574957/500000000000000000000000) where
  r0 := (506688772733/1000000000000000000)
  k0 := (3365188563896911/1000000000000000000)
  k6 := (5458220389771063/500000000000000000)
  q := (177392220798996707301/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15734]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15734]

theorem width_15735 : mW 15735 = 488690183601297 := by
  have hu : mW 15735 ≤ 488690183601297 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15735 ≤ 488690183601296 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15735 : RowArithmetic 15735 (1078832962553180691459/1000000000000000000000000) (118349549979083116771293/200000000000000000000000) (1079889436787073/200000000000000000000000) where
  r0 := (3958128683/7812500000000000)
  k0 := (673005632556709/200000000000000000)
  k6 := (10916093889989311/1000000000000000000)
  q := (177397857935207323631/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15735]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15735]

theorem width_15736 : mW 15736 = 488798893580554 := by
  have hu : mW 15736 ≤ 488798893580554 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15736 ≤ 488798893580553 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15736 : RowArithmetic 15736 (269702922538824685257/250000000000000000000000) (295869361195509832535287/500000000000000000000000) (1349639317959427/250000000000000000000000) where
  r0 := (50659217779/100000000000000000)
  k0 := (3364867779513261/1000000000000000000)
  k6 := (2183149406700703/200000000000000000)
  q := (709613979569173933/4000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15736]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15736]

theorem width_15737 : mW 15737 = 488907620832087 := by
  have hu : mW 15737 ≤ 488907620832087 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15737 ≤ 488907620832086 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15737 : RowArithmetic 15737 (269697605566973581733/250000000000000000000000) (591729696008410528394117/1000000000000000000000000) (1079533512959253/200000000000000000000000) where
  r0 := (506543891827/1000000000000000000)
  k0 := (841176853518831/250000000000000000)
  k6 := (10915400210079483/1000000000000000000)
  q := (88704565835136130269/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15737]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15737]

theorem width_15738 : mW 15738 = 489016365357542 := by
  have hu : mW 15738 ≤ 489016365357542 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15738 ≤ 489016365357541 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15738 : RowArithmetic 15738 (1078769158889715218323/1000000000000000000000000) (591720670747365283382841/1000000000000000000000000) (539677806275037/100000000000000000000000) where
  r0 := (101299122707/200000000000000000)
  k0 := (841136766618071/250000000000000000)
  k6 := (2183010683942393/200000000000000000)
  q := (4435369206729018179/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15738]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15738]

theorem width_15739 : mW 15739 = 489125127158566 := by
  have hu : mW 15739 ≤ 489125127158566 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15739 ≤ 489125127158565 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15739 : RowArithmetic 15739 (1078747900019509333121/1000000000000000000000000) (591711646607661228211857/1000000000000000000000000) (674486095704921/125000000000000000000000) where
  r0 := (506447342911/1000000000000000000)
  k0 := (3364386736696727/1000000000000000000)
  k6 := (2728676665598927/250000000000000000)
  q := (177420404688975952071/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15739]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15739]

theorem width_15740 : mW 15740 = 489233906236807 := by
  have hu : mW 15740 ≤ 489233906236807 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15740 ≤ 489233906236806 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15740 : RowArithmetic 15740 (1078726645656024738357/1000000000000000000000000) (147925655897268899809423/250000000000000000000000) (674374959175327/125000000000000000000000) where
  r0 := (506399079953/1000000000000000000)
  k0 := (1682113212372279/500000000000000000)
  k6 := (1364294992265683/125000000000000000)
  q := (177426040929735001513/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15740]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15740]

theorem width_15741 : mW 15741 = 489342702593909 := by
  have hu : mW 15741 ≤ 489342702593909 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15741 ≤ 489342702593908 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15741 : RowArithmetic 15741 (215741079159602225979/200000000000000000000000) (147923400422846442459347/250000000000000000000000) (2697055392989769/500000000000000000000000) where
  r0 := (506350824661/1000000000000000000)
  k0 := (1682033065309163/500000000000000000)
  k6 := (682125827930999/62500000000000000)
  q := (177431676991454939019/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15741]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15741]

theorem width_15742 : mW 15742 = 489451516231521 := by
  have hu : mW 15742 ≤ 489451516231521 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15742 ≤ 489451516231520 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15742 : RowArithmetic 15742 (53934207522210858407/50000000000000000000000) (591684580914369111977887/1000000000000000000000000) (2696611051654761/500000000000000000000000) where
  r0 := (63287822129/125000000000000000)
  k0 := (3363905854310611/1000000000000000000)
  k6 := (545683329435101/50000000000000000)
  q := (17743731287415282541/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15742]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15742]

theorem width_15743 : mW 15743 = 489560347151288 := by
  have hu : mW 15743 ≤ 489560347151288 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15743 ≤ 489560347151287 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15743 : RowArithmetic 15743 (539331454796696570743/500000000000000000000000) (147918890314450787691299/250000000000000000000000) (1348083406333007/250000000000000000000000) where
  r0 := (101250867413/200000000000000000)
  k0 := (21023409973879/6250000000000000)
  k6 := (10913319963538327/1000000000000000000)
  q := (443607371444614297/2500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15743]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15743]

theorem width_15744 : mW 15744 = 489669195354858 := by
  have hu : mW 15744 ≤ 489669195354858 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15744 ≤ 489669195354857 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15744 : RowArithmetic 15744 (215728334648857779017/200000000000000000000000) (5916665427214653716359/10000000000000000000000) (10782890703973/2000000000000000000000) where
  r0 := (506206104757/1000000000000000000)
  k0 := (26278010587039/7812500000000000)
  k6 := (545648668569983/50000000000000000)
  q := (177448584102550674593/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15744]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15744]

theorem width_15745 : mW 15745 = 489778060843878 := by
  have hu : mW 15745 ≤ 489778060843878 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15745 ≤ 489778060843877 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15745 : RowArithmetic 15745 (539310220697827507021/500000000000000000000000) (591657525305133414669957/1000000000000000000000000) (5390557283212419/1000000000000000000000000) where
  r0 := (126539470027/250000000000000000)
  k0 := (840856283068553/250000000000000000)
  k6 := (5456313406140387/500000000000000000)
  q := (35490843889656949097/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15745]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15745]

theorem width_15746 : mW 15746 = 489886943619993 := by
  have hu : mW 15746 ≤ 489886943619993 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15746 ≤ 489886943619992 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15746 : RowArithmetic 15746 (1078599214046243117989/1000000000000000000000000) (591648509008584896326641/1000000000000000000000000) (538966941894931/100000000000000000000000) where
  r0 := (126527415779/250000000000000000)
  k0 := (1681632463608101/500000000000000000)
  k6 := (2728070071544107/250000000000000000)
  q := (177459854615064981463/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15746]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15746]

theorem width_15747 : mW 15747 = 489995843684852 := by
  have hu : mW 15747 ≤ 489995843684852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15747 ≤ 489995843684851 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15747 : RowArithmetic 15747 (134822248899350511059/125000000000000000000000) (591639493831597524439951/1000000000000000000000000) (215551270365467/40000000000000000000000) where
  r0 := (253030726889/500000000000000000)
  k0 := (3363104739959537/1000000000000000000)
  k6 := (10911933793081379/1000000000000000000)
  q := (177465489602908429809/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15747]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15747]

theorem width_15748 : mW 15748 = 490104761040101 := by
  have hu : mW 15748 ≤ 490104761040101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15748 ≤ 490104761040100 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15748 : RowArithmetic 15748 (1078556772840090136707/1000000000000000000000000) (73953809971743633955827/125000000000000000000000) (5387894303714071/1000000000000000000000000) where
  r0 := (506013252093/1000000000000000000)
  k0 := (1681472285251719/500000000000000000)
  k6 := (10911587332990387/1000000000000000000)
  q := (177471124411832135099/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15748]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15748]

theorem width_15749 : mW 15749 = 490213695687388 := by
  have hu : mW 15749 ≤ 490213695687388 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15749 ≤ 490213695687387 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15749 : RowArithmetic 15749 (134816944872606665841/125000000000000000000000) (591621466835417407739863/1000000000000000000000000) (5387007052621059/1000000000000000000000000) where
  r0 := (25298252903/50000000000000000)
  k0 := (1681392209423563/500000000000000000)
  k6 := (10911240905898213/1000000000000000000)
  q := (27730743600289553/156250000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15749]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15749]

theorem width_15750 : mW 15750 = 490322647628358 := by
  have hu : mW 15750 ≤ 490322647628358 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15750 ≤ 490322647628357 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15750 : RowArithmetic 15750 (1078514349615847050741/1000000000000000000000000) (591612455015780390683277/1000000000000000000000000) (5386120005797251/1000000000000000000000000) where
  r0 := (126479217919/250000000000000000)
  k0 := (1681312142491587/500000000000000000)
  k6 := (545544725589981/50000000000000000)
  q := (88741196746494240639/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15750]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15750]

theorem width_15751 : mW 15751 = 490431616864660 := by
  have hu : mW 15751 ≤ 490431616864660 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15751 ≤ 490431616864659 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15751 : RowArithmetic 15751 (269623286185955990949/250000000000000000000000) (591603444314816019872027/1000000000000000000000000) (33657707269889/6250000000000000000000) where
  r0 := (505868692941/1000000000000000000)
  k0 := (840616042228531/250000000000000000)
  k6 := (10910548150689369/1000000000000000000)
  q := (17748802776525519779/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15751]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15751]

theorem width_15752 : mW 15752 = 490540603397941 := by
  have hu : mW 15752 ≤ 490540603397941 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15752 ≤ 490540603397940 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15752 : RowArithmetic 15752 (1078471944363537753813/1000000000000000000000000) (59159443473230225189499/100000000000000000000000) (2692173262357831/500000000000000000000000) where
  r0 := (126455130463/250000000000000000)
  k0 := (840576017658137/250000000000000000)
  k6 := (10910201822562227/1000000000000000000)
  q := (88746830929335161247/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15752]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15752]

theorem width_15753 : mW 15753 = 490649607229848 := by
  have hu : mW 15753 ≤ 490649607229848 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15753 ≤ 490649607229847 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15753 : RowArithmetic 15753 (26961268711843563779/25000000000000000000000) (591585426268017214162203/1000000000000000000000000) (5383460090337177/1000000000000000000000000) where
  r0 := (505772358407/1000000000000000000)
  k0 := (3362143990134339/1000000000000000000)
  k6 := (10909855527412957/1000000000000000000)
  q := (177499295773250886439/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15753]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15753]

theorem width_15754 : mW 15754 = 490758628362028 := by
  have hu : mW 15754 ≤ 490758628362028 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15754 ≤ 490758628362027 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15754 : RowArithmetic 15754 (215685911414638585689/200000000000000000000000) (73947052365217375016963/125000000000000000000000) (5382573859986467/1000000000000000000000000) where
  r0 := (252862101303/500000000000000000)
  k0 := (3361983927422037/1000000000000000000)
  k6 := (10909509265236327/1000000000000000000)
  q := (177504929509013917977/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15754]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15754]

theorem width_15755 : mW 15755 = 490867666796129 := by
  have hu : mW 15755 ≤ 490867666796129 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15755 ≤ 490867666796128 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15755 : RowArithmetic 15755 (67400523135040225373/62500000000000000000000) (591567412693245872597873/1000000000000000000000000) (5381687833603223/1000000000000000000000000) where
  r0 := (101135210889/200000000000000000)
  k0 := (1680911941242443/500000000000000000)
  k6 := (2181832607205421/200000000000000000)
  q := (88755281532988221377/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15755]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15755]

theorem width_15756 : mW 15756 = 490976722533797 := by
  have hu : mW 15756 ≤ 490976722533797 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15756 ≤ 490976722533796 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15756 : RowArithmetic 15756 (16849799808357036481/15625000000000000000000) (591558407582316030978531/1000000000000000000000000) (2690401005563591/500000000000000000000000) where
  r0 := (126406978481/250000000000000000)
  k0 := (1680831927662713/500000000000000000)
  k6 := (545440841989003/50000000000000000)
  q := (88758098222077741857/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15756]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15756]

theorem width_15757 : mW 15757 = 491085795576681 := by
  have hu : mW 15757 ≤ 491085795576681 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15757 ≤ 491085795576680 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15757 : RowArithmetic 15757 (269591502448642106187/250000000000000000000000) (73943675448590976436431/125000000000000000000000) (672489549062259/125000000000000000000000) where
  r0 := (505579781041/1000000000000000000)
  k0 := (672300769187909/200000000000000000)
  k6 := (10908470676489961/1000000000000000000)
  q := (177521829643568061103/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15757]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15757]

theorem width_15758 : mW 15758 = 491194885926429 := by
  have hu : mW 15758 ≤ 491194885926429 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15758 ≤ 491194885926428 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15758 : RowArithmetic 15758 (1078344836338553922039/1000000000000000000000000) (295770200356129785501227/500000000000000000000000) (1344757744413913/250000000000000000000000) where
  r0 := (101106331159/200000000000000000)
  k0 := (3361343854326459/1000000000000000000)
  k6 := (10908124546151581/1000000000000000000)
  q := (35505492532846238493/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15758]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15758]

theorem width_15759 : mW 15759 = 491303993584686 := by
  have hu : mW 15759 ≤ 491303993584686 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15759 ≤ 491303993584685 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15759 : RowArithmetic 15759 (1078323667365564196247/1000000000000000000000000) (591531398952689776653493/1000000000000000000000000) (672268220817467/125000000000000000000000) where
  r0 := (252741769091/500000000000000000)
  k0 := (672236776095081/200000000000000000)
  k6 := (1090777844875969/100000000000000000)
  q := (177533095506161892643/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15759]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15759]

theorem width_15760 : mW 15760 = 491413118553102 := by
  have hu : mW 15760 ≤ 491413118553102 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15760 ≤ 491413118553101 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15760 : RowArithmetic 15760 (215660500574871117617/200000000000000000000000) (118304479661959387058091/200000000000000000000000) (1344315189772527/250000000000000000000000) where
  r0 := (505435428203/1000000000000000000)
  k0 := (1680511962196123/500000000000000000)
  k6 := (1363429048038633/125000000000000000)
  q := (177538728169377173783/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15760]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15760]

theorem width_15761 : mW 15761 = 491522260833324 := by
  have hu : mW 15761 ≤ 491522260833324 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15761 ≤ 491522260833323 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15761 : RowArithmetic 15761 (539140671431842880743/500000000000000000000000) (59151339878335959050413/100000000000000000000000) (1075275191049321/200000000000000000000000) where
  r0 := (252693662927/500000000000000000)
  k0 := (3360863986066217/1000000000000000000)
  k6 := (10907086352794477/1000000000000000000)
  q := (44386090163473511333/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15761]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15761]

theorem width_15762 : mW 15762 = 491631420426999 := by
  have hu : mW 15762 ≤ 491631420426999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15762 ≤ 491631420426998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15762 : RowArithmetic 15762 (215652037466462564201/200000000000000000000000) (591504400373156357877153/1000000000000000000000000) (1075098270989817/200000000000000000000000) where
  r0 := (101067846227/200000000000000000)
  k0 := (672140813099971/200000000000000000)
  k6 := (2181348070842141/200000000000000000)
  q := (88774996479864757019/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15762]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15762]

theorem width_15763 : mW 15763 = 491740597335776 := by
  have hu : mW 15763 ≤ 491740597335776 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15763 ≤ 491740597335775 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15763 : RowArithmetic 15763 (539119518139497362327/500000000000000000000000) (2957477015394829691607/5000000000000000000000) (5374606958137411/1000000000000000000000000) where
  r0 := (505291144043/1000000000000000000)
  k0 := (1680272081342859/500000000000000000)
  k6 := (436255775542101/40000000000000000)
  q := (177555625086900583951/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15763]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15763]

theorem width_15764 : mW 15764 = 491849791561301 := by
  have hu : mW 15764 ≤ 491849791561301 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15764 ≤ 491849791561300 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15764 : RowArithmetic 15764 (1078217889702490751649/1000000000000000000000000) (118297281380113407991067/200000000000000000000000) (5373722764751497/1000000000000000000000000) where
  r0 := (252621532289/500000000000000000)
  k0 := (3360384277626341/1000000000000000000)
  k6 := (2726512113953679/250000000000000000)
  q := (177561257035424256427/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15764]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15764]

theorem width_15765 : mW 15765 = 491959003105224 := by
  have hu : mW 15765 ≤ 491959003105224 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15765 ≤ 491959003105223 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15765 : RowArithmetic 15765 (539098373800779723863/500000000000000000000000) (591477411837738509286501/1000000000000000000000000) (1343209693682809/250000000000000000000000) where
  r0 := (15787343523/31250000000000000)
  k0 := (672044882062191/200000000000000000)
  k6 := (1363212819499007/125000000000000000)
  q := (177566888805317530123/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15765]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15765]

theorem width_15766 : mW 15766 = 492068231969192 := by
  have hu : mW 15766 ≤ 492068231969192 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15766 ≤ 492068231969191 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15766 : RowArithmetic 15766 (539087804987480339603/500000000000000000000000) (73933552236282391517823/125000000000000000000000) (2685977494008289/500000000000000000000000) where
  r0 := (505146928517/1000000000000000000)
  k0 := (3360064560742093/1000000000000000000)
  k6 := (5452678344539663/500000000000000000)
  q := (88786260198298700501/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15766]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15766]

theorem width_15767 : mW 15767 = 492177478154853 := by
  have hu : mW 15767 ≤ 492177478154853 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15767 ≤ 492177478154852 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15767 : RowArithmetic 15767 (269538619205363614743/250000000000000000000000) (591459425057907929981947/1000000000000000000000000) (2685535702273741/500000000000000000000000) where
  r0 := (6313735899/12500000000000000)
  k0 := (1679952364459481/500000000000000000)
  k6 := (10905010855071309/1000000000000000000)
  q := (44394537952320215583/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15767]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15767]

theorem width_15768 : mW 15768 = 492286741663855 := by
  have hu : mW 15768 ≤ 492286741663855 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15768 ≤ 492286741663854 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15768 : RowArithmetic 15768 (134766668517475154969/125000000000000000000000) (295725216670231920042501/500000000000000000000000) (5370188024263931/1000000000000000000000000) where
  r0 := (505050822941/1000000000000000000)
  k0 := (335974491483079/100000000000000000)
  k6 := (5452332526981393/500000000000000000)
  q := (88791891521692452343/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15768]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15768]

theorem width_15769 : mW 15769 = 492396022497846 := by
  have hu : mW 15769 ≤ 492396022497846 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15769 ≤ 492396022497845 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15769 : RowArithmetic 15769 (1078112223928761913911/1000000000000000000000000) (147860360684426472734643/250000000000000000000000) (536930484710593/100000000000000000000000) where
  r0 := (25250139079/50000000000000000)
  k0 := (839896279620027/250000000000000000)
  k6 := (10904319285748543/1000000000000000000)
  q := (88794707049463257971/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15769]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15769]

theorem width_15770 : mW 15770 = 492505320658474 := by
  have hu : mW 15770 ≤ 492505320658474 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15770 ≤ 492505320658473 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15770 : RowArithmetic 15770 (1078091104187097813257/1000000000000000000000000) (591432453249413174065829/1000000000000000000000000) (20970397941459/3906250000000000000000) where
  r0 := (252477373917/500000000000000000)
  k0 := (839856334964867/250000000000000000)
  k6 := (10903973550423363/1000000000000000000)
  q := (22199380621990335161/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15770]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15770]

theorem width_15771 : mW 15771 = 492614636147387 := by
  have hu : mW 15771 ≤ 492614636147387 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15771 ≤ 492614636147386 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15771 : RowArithmetic 15771 (539034994456785354417/500000000000000000000000) (591423464875364897259961/1000000000000000000000000) (335471193870419/62500000000000000000000) where
  r0 := (504906721703/1000000000000000000)
  k0 := (16796327894857/5000000000000000)
  k6 := (2180725569596407/200000000000000000)
  q := (11100042229649398951/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15771]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15771]

theorem width_15772 : mW 15772 = 492723968966235 := by
  have hu : mW 15772 ≤ 492723968966235 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15772 ≤ 492723968966234 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15772 : RowArithmetic 15772 (134756109763367778213/125000000000000000000000) (147853619403835054510883/250000000000000000000000) (2683328266892789/500000000000000000000000) where
  r0 := (100971740637/200000000000000000)
  k0 := (3359105835811779/1000000000000000000)
  k6 := (681455136151209/62500000000000000)
  q := (177606306194346601529/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15772]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15772]

theorem width_15773 : mW 15773 = 492833319116664 := by
  have hu : mW 15773 ≤ 492833319116664 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15773 ≤ 492833319116663 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15773 : RowArithmetic 15773 (215605554353195119647/200000000000000000000000) (591405491469118517545459/1000000000000000000000000) (5365774168530241/1000000000000000000000000) where
  r0 := (504810692277/1000000000000000000)
  k0 := (839736527593289/250000000000000000)
  k6 := (10902936541730081/1000000000000000000)
  q := (22201492066976039167/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15773]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15773]

theorem width_15774 : mW 15774 = 492942686600323 := by
  have hu : mW 15774 ≤ 492942686600323 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15774 ≤ 492942686600322 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15774 : RowArithmetic 15774 (1078006669889433621683/1000000000000000000000000) (73924563304559880885017/125000000000000000000000) (2682446003050399/500000000000000000000000) where
  r0 := (252381344489/500000000000000000)
  k0 := (335878640265473/100000000000000000)
  k6 := (5451295468954517/500000000000000000)
  q := (177617566698792493057/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15774]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15774]

theorem width_15775 : mW 15775 = 493052071418862 := by
  have hu : mW 15775 ≤ 493052071418862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15775 ≤ 493052071418861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15775 : RowArithmetic 15775 (1077985572476079237981/1000000000000000000000000) (591387522517201237523/1000000000000000000000) (1341002511609341/250000000000000000000000) where
  r0 := (252357346643/500000000000000000)
  k0 := (419828339081547/125000000000000000)
  k6 := (2725561341737749/250000000000000000)
  q := (88811598341658056211/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15775]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15775]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15701 then ⟨(134944864598205489963/125000000000000000000000), (592055354103056416755951/1000000000000000000000000), (5429826638348373/1000000000000000000000000)⟩ else
  if n = 15702 then ⟨(1079537490283289148989/1000000000000000000000000), (592046288324889129418411/1000000000000000000000000), (2714464859041443/500000000000000000000000)⟩ else
  if n = 15703 then ⟨(269879017083562199919/250000000000000000000000), (592037223676121303844031/1000000000000000000000000), (542803300494953/100000000000000000000000)⟩ else
  if n = 15704 then ⟨(8433551960447317177/7812500000000000000000), (74003520019566002219059/125000000000000000000000), (21199751948777/3906250000000000000000)⟩ else
  if n = 15705 then ⟨(1079473238091045523553/1000000000000000000000000), (118403819553176879566069/200000000000000000000000), (5426240199833619/1000000000000000000000000)⟩ else
  if n = 15706 then ⟨(1079451829794349603121/1000000000000000000000000), (148002509125991407867553/250000000000000000000000), (2712672053864141/500000000000000000000000)⟩ else
  if n = 15707 then ⟨(134928803255737839681/125000000000000000000000), (296000488185273503250611/500000000000000000000000), (1356112055627383/250000000000000000000000)⟩ else
  if n = 15708 then ⟨(539704513422219748691/500000000000000000000000), (591991917365403887675703/1000000000000000000000000), (1084710508823207/200000000000000000000000)⟩ else
  if n = 15709 then ⟨(1079387632188695623169/1000000000000000000000000), (295991429744155813372047/500000000000000000000000), (2711328536243251/500000000000000000000000)⟩ else
  if n = 15710 then ⟨(1079366242077406027413/1000000000000000000000000), (73996725342380710415099/125000000000000000000000), (2710880903779811/500000000000000000000000)⟩ else
  if n = 15711 then ⟨(215868971301861338429/200000000000000000000000), (295982373558690805757921/500000000000000000000000), (338804171829633/62500000000000000000000)⟩ else
  if n = 15712 then ⟨(1079323475483134348439/1000000000000000000000000), (591955692623094956864037/1000000000000000000000000), (1354992974392197/250000000000000000000000)⟩ else
  if n = 15713 then ⟨(539651049498812938873/500000000000000000000000), (591946639255961347697223/1000000000000000000000000), (5419077252382383/1000000000000000000000000)⟩ else
  if n = 15714 then ⟨(269820181762879578059/250000000000000000000000), (591937587015756533282191/1000000000000000000000000), (2709091406826851/500000000000000000000000)⟩ else
  if n = 15715 then ⟨(1079259359643549133881/1000000000000000000000000), (36995533493891012494009/62500000000000000000000), (5417288581321559/1000000000000000000000000)⟩ else
  if n = 15716 then ⟨(1079237996772456871491/1000000000000000000000000), (59191948591523623436411/100000000000000000000000), (5416394555324813/1000000000000000000000000)⟩ else
  if n = 15717 then ⟨(1079216638436980203869/1000000000000000000000000), (295955218527236254439349/500000000000000000000000), (1083100147120467/200000000000000000000000)⟩ else
  if n = 15718 then ⟨(4316781138543430647/4000000000000000000000), (73987673664967621757861/125000000000000000000000), (1082921424418599/200000000000000000000000)⟩ else
  if n = 15719 then ⟨(1079173935367828821869/1000000000000000000000000), (591892342710817592496801/1000000000000000000000000), (1353428428683927/250000000000000000000000)⟩ else
  if n = 15720 then ⟨(269788147657908427321/250000000000000000000000), (591883297227478475697347/1000000000000000000000000), (2706410256734707/500000000000000000000000)⟩ else
  if n = 15721 then ⟨(134891406303251599647/125000000000000000000000), (591874252869499736867081/1000000000000000000000000), (338245469889567/62500000000000000000000)⟩ else
  if n = 15722 then ⟨(539554957374853205357/500000000000000000000000), (295932604818328788903601/500000000000000000000000), (1082206945793129/200000000000000000000000)⟩ else
  if n = 15723 then ⟨(539544291800727959679/500000000000000000000000), (295928083764364104640643/500000000000000000000000), (5410142145606139/1000000000000000000000000)⟩ else
  if n = 15724 then ⟨(1079067256980002842331/1000000000000000000000000), (591847126545488030788499/1000000000000000000000000), (5409249768093571/1000000000000000000000000)⟩ else
  if n = 15725 then ⟨(1079045934884089146587/1000000000000000000000000), (59183808668671336098459/100000000000000000000000), (2704178798183491/500000000000000000000000)⟩ else
  if n = 15726 then ⟨(215804923462491508827/200000000000000000000000), (295914523976090315310119/500000000000000000000000), (2703732815182723/500000000000000000000000)⟩ else
  if n = 15727 then ⟨(215800660852770179291/200000000000000000000000), (7397750129270828861003/12500000000000000000000), (5406573870028049/1000000000000000000000000)⟩ else
  if n = 15728 then ⟨(215796399147402442969/200000000000000000000000), (295905486927473504749527/500000000000000000000000), (84463786176467/15625000000000000000000)⟩ else
  if n = 15729 then ⟨(539480345865342776169/500000000000000000000000), (591801938491799338857569/1000000000000000000000000), (1080958193220421/200000000000000000000000)⟩ else
  if n = 15730 then ⟨(67433712015225944447/62500000000000000000000), (591792904251999968413979/1000000000000000000000000), (5403899822391853/1000000000000000000000000)⟩ else
  if n = 15731 then ⟨(1078918097274545243039/1000000000000000000000000), (591783871135325627096911/1000000000000000000000000), (675376110512787/125000000000000000000000)⟩ else
  if n = 15732 then ⟨(215779361364444208669/200000000000000000000000), (591774839141553117607857/1000000000000000000000000), (1080423630234527/200000000000000000000000)⟩ else
  if n = 15733 then ⟨(1078875520885388350261/1000000000000000000000000), (29588290413522966115701/50000000000000000000000), (5401227623542101/1000000000000000000000000)⟩ else
  if n = 15734 then ⟨(539427119731396278749/500000000000000000000000), (591756778521821161928393/1000000000000000000000000), (2700168650574957/500000000000000000000000)⟩ else
  if n = 15735 then ⟨(1078832962553180691459/1000000000000000000000000), (118349549979083116771293/200000000000000000000000), (1079889436787073/200000000000000000000000)⟩ else
  if n = 15736 then ⟨(269702922538824685257/250000000000000000000000), (295869361195509832535287/500000000000000000000000), (1349639317959427/250000000000000000000000)⟩ else
  if n = 15737 then ⟨(269697605566973581733/250000000000000000000000), (591729696008410528394117/1000000000000000000000000), (1079533512959253/200000000000000000000000)⟩ else
  if n = 15738 then ⟨(1078769158889715218323/1000000000000000000000000), (591720670747365283382841/1000000000000000000000000), (539677806275037/100000000000000000000000)⟩ else
  if n = 15739 then ⟨(1078747900019509333121/1000000000000000000000000), (591711646607661228211857/1000000000000000000000000), (674486095704921/125000000000000000000000)⟩ else
  if n = 15740 then ⟨(1078726645656024738357/1000000000000000000000000), (147925655897268899809423/250000000000000000000000), (674374959175327/125000000000000000000000)⟩ else
  if n = 15741 then ⟨(215741079159602225979/200000000000000000000000), (147923400422846442459347/250000000000000000000000), (2697055392989769/500000000000000000000000)⟩ else
  if n = 15742 then ⟨(53934207522210858407/50000000000000000000000), (591684580914369111977887/1000000000000000000000000), (2696611051654761/500000000000000000000000)⟩ else
  if n = 15743 then ⟨(539331454796696570743/500000000000000000000000), (147918890314450787691299/250000000000000000000000), (1348083406333007/250000000000000000000000)⟩ else
  if n = 15744 then ⟨(215728334648857779017/200000000000000000000000), (5916665427214653716359/10000000000000000000000), (10782890703973/2000000000000000000000)⟩ else
  if n = 15745 then ⟨(539310220697827507021/500000000000000000000000), (591657525305133414669957/1000000000000000000000000), (5390557283212419/1000000000000000000000000)⟩ else
  if n = 15746 then ⟨(1078599214046243117989/1000000000000000000000000), (591648509008584896326641/1000000000000000000000000), (538966941894931/100000000000000000000000)⟩ else
  if n = 15747 then ⟨(134822248899350511059/125000000000000000000000), (591639493831597524439951/1000000000000000000000000), (215551270365467/40000000000000000000000)⟩ else
  if n = 15748 then ⟨(1078556772840090136707/1000000000000000000000000), (73953809971743633955827/125000000000000000000000), (5387894303714071/1000000000000000000000000)⟩ else
  if n = 15749 then ⟨(134816944872606665841/125000000000000000000000), (591621466835417407739863/1000000000000000000000000), (5387007052621059/1000000000000000000000000)⟩ else
  if n = 15750 then ⟨(1078514349615847050741/1000000000000000000000000), (591612455015780390683277/1000000000000000000000000), (5386120005797251/1000000000000000000000000)⟩ else
  if n = 15751 then ⟨(269623286185955990949/250000000000000000000000), (591603444314816019872027/1000000000000000000000000), (33657707269889/6250000000000000000000)⟩ else
  if n = 15752 then ⟨(1078471944363537753813/1000000000000000000000000), (59159443473230225189499/100000000000000000000000), (2692173262357831/500000000000000000000000)⟩ else
  if n = 15753 then ⟨(26961268711843563779/25000000000000000000000), (591585426268017214162203/1000000000000000000000000), (5383460090337177/1000000000000000000000000)⟩ else
  if n = 15754 then ⟨(215685911414638585689/200000000000000000000000), (73947052365217375016963/125000000000000000000000), (5382573859986467/1000000000000000000000000)⟩ else
  if n = 15755 then ⟨(67400523135040225373/62500000000000000000000), (591567412693245872597873/1000000000000000000000000), (5381687833603223/1000000000000000000000000)⟩ else
  if n = 15756 then ⟨(16849799808357036481/15625000000000000000000), (591558407582316030978531/1000000000000000000000000), (2690401005563591/500000000000000000000000)⟩ else
  if n = 15757 then ⟨(269591502448642106187/250000000000000000000000), (73943675448590976436431/125000000000000000000000), (672489549062259/125000000000000000000000)⟩ else
  if n = 15758 then ⟨(1078344836338553922039/1000000000000000000000000), (295770200356129785501227/500000000000000000000000), (1344757744413913/250000000000000000000000)⟩ else
  if n = 15759 then ⟨(1078323667365564196247/1000000000000000000000000), (591531398952689776653493/1000000000000000000000000), (672268220817467/125000000000000000000000)⟩ else
  if n = 15760 then ⟨(215660500574871117617/200000000000000000000000), (118304479661959387058091/200000000000000000000000), (1344315189772527/250000000000000000000000)⟩ else
  if n = 15761 then ⟨(539140671431842880743/500000000000000000000000), (59151339878335959050413/100000000000000000000000), (1075275191049321/200000000000000000000000)⟩ else
  if n = 15762 then ⟨(215652037466462564201/200000000000000000000000), (591504400373156357877153/1000000000000000000000000), (1075098270989817/200000000000000000000000)⟩ else
  if n = 15763 then ⟨(539119518139497362327/500000000000000000000000), (2957477015394829691607/5000000000000000000000), (5374606958137411/1000000000000000000000000)⟩ else
  if n = 15764 then ⟨(1078217889702490751649/1000000000000000000000000), (118297281380113407991067/200000000000000000000000), (5373722764751497/1000000000000000000000000)⟩ else
  if n = 15765 then ⟨(539098373800779723863/500000000000000000000000), (591477411837738509286501/1000000000000000000000000), (1343209693682809/250000000000000000000000)⟩ else
  if n = 15766 then ⟨(539087804987480339603/500000000000000000000000), (73933552236282391517823/125000000000000000000000), (2685977494008289/500000000000000000000000)⟩ else
  if n = 15767 then ⟨(269538619205363614743/250000000000000000000000), (591459425057907929981947/1000000000000000000000000), (2685535702273741/500000000000000000000000)⟩ else
  if n = 15768 then ⟨(134766668517475154969/125000000000000000000000), (295725216670231920042501/500000000000000000000000), (5370188024263931/1000000000000000000000000)⟩ else
  if n = 15769 then ⟨(1078112223928761913911/1000000000000000000000000), (147860360684426472734643/250000000000000000000000), (536930484710593/100000000000000000000000)⟩ else
  if n = 15770 then ⟨(1078091104187097813257/1000000000000000000000000), (591432453249413174065829/1000000000000000000000000), (20970397941459/3906250000000000000000)⟩ else
  if n = 15771 then ⟨(539034994456785354417/500000000000000000000000), (591423464875364897259961/1000000000000000000000000), (335471193870419/62500000000000000000000)⟩ else
  if n = 15772 then ⟨(134756109763367778213/125000000000000000000000), (147853619403835054510883/250000000000000000000000), (2683328266892789/500000000000000000000000)⟩ else
  if n = 15773 then ⟨(215605554353195119647/200000000000000000000000), (591405491469118517545459/1000000000000000000000000), (5365774168530241/1000000000000000000000000)⟩ else
  if n = 15774 then ⟨(1078006669889433621683/1000000000000000000000000), (73924563304559880885017/125000000000000000000000), (2682446003050399/500000000000000000000000)⟩ else
  ⟨(1077985572476079237981/1000000000000000000000000), (591387522517201237523/1000000000000000000000), (1341002511609341/250000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15701 ≤ n) (hb : n ≤ 15775) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15701
  · exact row_15702
  · exact row_15703
  · exact row_15704
  · exact row_15705
  · exact row_15706
  · exact row_15707
  · exact row_15708
  · exact row_15709
  · exact row_15710
  · exact row_15711
  · exact row_15712
  · exact row_15713
  · exact row_15714
  · exact row_15715
  · exact row_15716
  · exact row_15717
  · exact row_15718
  · exact row_15719
  · exact row_15720
  · exact row_15721
  · exact row_15722
  · exact row_15723
  · exact row_15724
  · exact row_15725
  · exact row_15726
  · exact row_15727
  · exact row_15728
  · exact row_15729
  · exact row_15730
  · exact row_15731
  · exact row_15732
  · exact row_15733
  · exact row_15734
  · exact row_15735
  · exact row_15736
  · exact row_15737
  · exact row_15738
  · exact row_15739
  · exact row_15740
  · exact row_15741
  · exact row_15742
  · exact row_15743
  · exact row_15744
  · exact row_15745
  · exact row_15746
  · exact row_15747
  · exact row_15748
  · exact row_15749
  · exact row_15750
  · exact row_15751
  · exact row_15752
  · exact row_15753
  · exact row_15754
  · exact row_15755
  · exact row_15756
  · exact row_15757
  · exact row_15758
  · exact row_15759
  · exact row_15760
  · exact row_15761
  · exact row_15762
  · exact row_15763
  · exact row_15764
  · exact row_15765
  · exact row_15766
  · exact row_15767
  · exact row_15768
  · exact row_15769
  · exact row_15770
  · exact row_15771
  · exact row_15772
  · exact row_15773
  · exact row_15774
  · exact row_15775

end BstLean.Part271.R3.Rows15701
