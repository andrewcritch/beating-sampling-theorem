import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15110–15128. -/
namespace BstLean.Part271.R3.Rows15110
open Real BstLean.Part130 BstLean.Part227

theorem width_15110 : mW 15110 = 424058355859296 := by
  have hu : mW 15110 ≤ 424058355859296 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15110 ≤ 424058355859295 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15110 : RowArithmetic 15110 (136633085476304037293/125000000000000000000000) (597618908533237613920509/1000000000000000000000000) (299919279043971/50000000000000000000000) where
  r0 := (53839783333/100000000000000000)
  k0 := (3468889098101221/1000000000000000000)
  k6 := (2227913881801841/200000000000000000)
  q := (173839005979670742019/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15110]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15110]

theorem width_15111 : mW 15111 = 424156590606672 := by
  have hu : mW 15111 ≤ 424156590606672 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15111 ≤ 424156590606671 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15111 : RowArithmetic 15111 (1093040328608845353403/1000000000000000000000000) (298804566845560728604177/500000000000000000000000) (5997354679901589/1000000000000000000000000) where
  r0 := (538344389919/1000000000000000000)
  k0 := (3468716926284077/1000000000000000000)
  k6 := (2784800202876757/250000000000000000)
  q := (34768951666681007367/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15111]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15111]

theorem width_15112 : mW 15112 = 424254841607584 := by
  have hu : mW 15112 ≤ 424254841607584 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15112 ≤ 424254841607583 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15112 : RowArithmetic 15112 (17078374668628840089/15625000000000000000000) (597599360122881518073329/1000000000000000000000000) (599632402660031/100000000000000000000000) where
  r0 := (538290955349/1000000000000000000)
  k0 := (34685447744047/10000000000000000)
  k6 := (5569416125296013/500000000000000000)
  q := (173850510496805847027/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15112]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15112]

theorem width_15113 : mW 15113 = 424353108863645 := by
  have hu : mW 15113 ≤ 424353108863645 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15113 ≤ 424353108863644 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15113 : RowArithmetic 15113 (54649581717953741377/50000000000000000000000) (149397396957063104086663/250000000000000000000000) (599529362089919/100000000000000000000000) where
  r0 := (538237529617/1000000000000000000)
  k0 := (693674528491279/200000000000000000)
  k6 := (2784615931564537/250000000000000000)
  q := (17385626246989206457/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15113]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15113]

theorem width_15114 : mW 15114 = 424451392376470 := by
  have hu : mW 15114 ≤ 424451392376470 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15114 ≤ 424451392376469 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15114 : RowArithmetic 15114 (1092967295307773658867/1000000000000000000000000) (119515963361393784988323/200000000000000000000000) (2997131731360917/500000000000000000000000) where
  r0 := (538184112723/1000000000000000000)
  k0 := (3468200530442127/1000000000000000000)
  k6 := (5569047619249671/500000000000000000)
  q := (173862014252682578313/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15114]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15114]

theorem width_15115 : mW 15115 = 424549692147671 := by
  have hu : mW 15115 ≤ 424549692147671 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15115 ≤ 424549692147670 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15115 : RowArithmetic 15115 (273235740409196270419/250000000000000000000000) (298785023529382863325701/500000000000000000000000) (74915419399899/12500000000000000000000) where
  r0 := (67266338083/125000000000000000)
  k0 := (3468028438355199/1000000000000000000)
  k6 := (11137726787309559/1000000000000000000)
  q := (86933882922598136989/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15115]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15115]

theorem width_15116 : mW 15116 = 424648008178862 := by
  have hu : mW 15116 ≤ 424648008178862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15116 ≤ 424648008178861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15116 : RowArithmetic 15116 (1092918633344551745027/1000000000000000000000000) (597560278583377810737001/1000000000000000000000000) (749025486079141/125000000000000000000000) where
  r0 := (538077305437/1000000000000000000)
  k0 := (346785636618891/100000000000000000)
  k6 := (44549433490731/4000000000000000)
  q := (173873517247452034167/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15116]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15116]

theorem width_15117 : mW 15117 = 424746340471658 := by
  have hu : mW 15117 ≤ 424746340471658 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15117 ≤ 424746340471657 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15117 : RowArithmetic 15117 (1092894310429516500577/1000000000000000000000000) (597550511380540042229007/1000000000000000000000000) (93612101133893/15625000000000000000000) where
  r0 := (269011957521/500000000000000000)
  k0 := (138707372557849/40000000000000000)
  k6 := (1113698999461287/100000000000000000)
  q := (86939634229734369179/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15117]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15117]

theorem width_15118 : mW 15118 = 424844689027670 := by
  have hu : mW 15118 ≤ 424844689027670 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15118 ≤ 424844689027669 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15118 : RowArithmetic 15118 (1092869992890124274147/1000000000000000000000000) (298770372724993759458033/500000000000000000000000) (2995072651861887/500000000000000000000000) where
  r0 := (21518821339/40000000000000000)
  k0 := (3467512281617219/1000000000000000000)
  k6 := (696038853318367/62500000000000000)
  q := (34777003896253052581/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15118]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15118]

theorem width_15119 : mW 15119 = 424943053848515 := by
  have hu : mW 15119 ≤ 424943053848515 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15119 ≤ 424943053848514 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15119 : RowArithmetic 15119 (1092845680724818321757/1000000000000000000000000) (597530980791455304508033/1000000000000000000000000) (5989116382020719/1000000000000000000000000) where
  r0 := (107583432147/200000000000000000)
  k0 := (3467340269201633/1000000000000000000)
  k6 := (11136253348119713/1000000000000000000)
  q := (173890770312860481043/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15119]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15119]

theorem width_15120 : mW 15120 = 425041434935804 := by
  have hu : mW 15120 ≤ 425041434935804 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15120 ≤ 425041434935803 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15120 : RowArithmetic 15120 (546410686966022360457/500000000000000000000000) (37345076087792412279297/62500000000000000000000) (2994043853691913/500000000000000000000000) where
  r0 := (26893189841/50000000000000000)
  k0 := (693433655339197/200000000000000000)
  k6 := (222717701593687/20000000000000000)
  q := (34779304190854652577/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15120]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15120]

theorem width_15121 : mW 15121 = 425139832291153 := by
  have hu : mW 15121 ≤ 425139832291153 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15121 ≤ 425139832291152 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15121 : RowArithmetic 15121 (546398536255124127147/500000000000000000000000) (597511455289392627387517/1000000000000000000000000) (5987059279736893/1000000000000000000000000) where
  r0 := (537810441727/1000000000000000000)
  k0 := (3466996304093567/1000000000000000000)
  k6 := (5567758423890871/500000000000000000)
  q := (6956090856220899017/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15121]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15121]

theorem width_15122 : mW 15122 = 425238245916174 := by
  have hu : mW 15122 ≤ 425238245916174 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15122 ≤ 425238245916173 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15122 : RowArithmetic 15122 (546386388228937887953/500000000000000000000000) (74687711805666590678839/125000000000000000000000) (2993015549501903/500000000000000000000000) where
  r0 := (107551419091/200000000000000000)
  k0 := (3466824351394119/1000000000000000000)
  k6 := (1391893581550731/125000000000000000)
  q := (34781604333325396507/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15122]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15122]

theorem width_15123 : mW 15123 = 425336675812482 := by
  have hu : mW 15123 ≤ 425336675812482 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15123 ≤ 425336675812481 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15123 : RowArithmetic 15123 (273187121443343398351/250000000000000000000000) (23899677394889372391139/40000000000000000000000) (1496250791277109/250000000000000000000000) where
  r0 := (537703758001/1000000000000000000)
  k0 := (3466652418590931/1000000000000000000)
  k6 := (1391847561693829/125000000000000000)
  q := (173913771737605644973/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15123]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15123]

theorem width_15124 : mW 15124 = 425435121981692 := by
  have hu : mW 15124 ≤ 425435121981692 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15124 ≤ 425435121981691 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15124 : RowArithmetic 15124 (21854484009103771801/20000000000000000000000) (597482176569832839208293/1000000000000000000000000) (5983975477974683/1000000000000000000000000) where
  r0 := (107530085873/200000000000000000)
  k0 := (693296101137393/200000000000000000)
  k6 := (2226882474242011/200000000000000000)
  q := (86959760809238660187/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15124]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15124]

theorem width_15125 : mW 15125 = 425533584425416 := by
  have hu : mW 15125 ≤ 425533584425416 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15125 ≤ 425533584425415 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15125 : RowArithmetic 15125 (1092699920501769344097/1000000000000000000000000) (298736209768931952406091/500000000000000000000000) (5982948037526519/1000000000000000000000000) where
  r0 := (268798554771/500000000000000000)
  k0 := (173315430633453/50000000000000000)
  k6 := (11134044285378083/1000000000000000000)
  q := (8696263565463043163/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15125]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15125]

theorem width_15126 : mW 15126 = 425632063145270 := by
  have hu : mW 15126 ≤ 425632063145270 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15126 ≤ 425632063145269 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15126 : RowArithmetic 15126 (546337822955781757417/500000000000000000000000) (597462663776063082475979/1000000000000000000000000) (1495480210921973/250000000000000000000000) where
  r0 := (134385949633/250000000000000000)
  k0 := (216633546221261/62500000000000000)
  k6 := (278341905901217/25000000000000000)
  q := (43482755202493781259/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15126]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15126]

theorem width_15127 : mW 15127 = 425730558142867 := by
  have hu : mW 15127 ≤ 425730558142867 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15127 ≤ 425730558142866 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15127 : RowArithmetic 15127 (218530275336604091141/200000000000000000000000) (298726454642083071293023/500000000000000000000000) (186902934261963/31250000000000000000000) where
  r0 := (537490496333/1000000000000000000)
  k0 := (433245610787103/125000000000000000)
  k6 := (2226661644643163/200000000000000000)
  q := (43484192530159738497/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15127]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15127]

theorem width_15128 : mW 15128 = 425829069419821 := by
  have hu : mW 15128 ≤ 425829069419821 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15128 ≤ 425829069419820 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15128 : RowArithmetic 15128 (273156778203647430181/250000000000000000000000) (59744315606190878413167/100000000000000000000000) (2989933597767663/500000000000000000000000) where
  r0 := (268718601471/500000000000000000)
  k0 := (3465793052932287/1000000000000000000)
  k6 := (695808765429591/62500000000000000)
  q := (173942519241271195291/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15128]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15128]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15110 then ⟨(136633085476304037293/125000000000000000000000), (597618908533237613920509/1000000000000000000000000), (299919279043971/50000000000000000000000)⟩ else
  if n = 15111 then ⟨(1093040328608845353403/1000000000000000000000000), (298804566845560728604177/500000000000000000000000), (5997354679901589/1000000000000000000000000)⟩ else
  if n = 15112 then ⟨(17078374668628840089/15625000000000000000000), (597599360122881518073329/1000000000000000000000000), (599632402660031/100000000000000000000000)⟩ else
  if n = 15113 then ⟨(54649581717953741377/50000000000000000000000), (149397396957063104086663/250000000000000000000000), (599529362089919/100000000000000000000000)⟩ else
  if n = 15114 then ⟨(1092967295307773658867/1000000000000000000000000), (119515963361393784988323/200000000000000000000000), (2997131731360917/500000000000000000000000)⟩ else
  if n = 15115 then ⟨(273235740409196270419/250000000000000000000000), (298785023529382863325701/500000000000000000000000), (74915419399899/12500000000000000000000)⟩ else
  if n = 15116 then ⟨(1092918633344551745027/1000000000000000000000000), (597560278583377810737001/1000000000000000000000000), (749025486079141/125000000000000000000000)⟩ else
  if n = 15117 then ⟨(1092894310429516500577/1000000000000000000000000), (597550511380540042229007/1000000000000000000000000), (93612101133893/15625000000000000000000)⟩ else
  if n = 15118 then ⟨(1092869992890124274147/1000000000000000000000000), (298770372724993759458033/500000000000000000000000), (2995072651861887/500000000000000000000000)⟩ else
  if n = 15119 then ⟨(1092845680724818321757/1000000000000000000000000), (597530980791455304508033/1000000000000000000000000), (5989116382020719/1000000000000000000000000)⟩ else
  if n = 15120 then ⟨(546410686966022360457/500000000000000000000000), (37345076087792412279297/62500000000000000000000), (2994043853691913/500000000000000000000000)⟩ else
  if n = 15121 then ⟨(546398536255124127147/500000000000000000000000), (597511455289392627387517/1000000000000000000000000), (5987059279736893/1000000000000000000000000)⟩ else
  if n = 15122 then ⟨(546386388228937887953/500000000000000000000000), (74687711805666590678839/125000000000000000000000), (2993015549501903/500000000000000000000000)⟩ else
  if n = 15123 then ⟨(273187121443343398351/250000000000000000000000), (23899677394889372391139/40000000000000000000000), (1496250791277109/250000000000000000000000)⟩ else
  if n = 15124 then ⟨(21854484009103771801/20000000000000000000000), (597482176569832839208293/1000000000000000000000000), (5983975477974683/1000000000000000000000000)⟩ else
  if n = 15125 then ⟨(1092699920501769344097/1000000000000000000000000), (298736209768931952406091/500000000000000000000000), (5982948037526519/1000000000000000000000000)⟩ else
  if n = 15126 then ⟨(546337822955781757417/500000000000000000000000), (597462663776063082475979/1000000000000000000000000), (1495480210921973/250000000000000000000000)⟩ else
  if n = 15127 then ⟨(218530275336604091141/200000000000000000000000), (298726454642083071293023/500000000000000000000000), (186902934261963/31250000000000000000000)⟩ else
  ⟨(273156778203647430181/250000000000000000000000), (59744315606190878413167/100000000000000000000000), (2989933597767663/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15110 ≤ n) (hb : n ≤ 15128) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15110
  · exact row_15111
  · exact row_15112
  · exact row_15113
  · exact row_15114
  · exact row_15115
  · exact row_15116
  · exact row_15117
  · exact row_15118
  · exact row_15119
  · exact row_15120
  · exact row_15121
  · exact row_15122
  · exact row_15123
  · exact row_15124
  · exact row_15125
  · exact row_15126
  · exact row_15127
  · exact row_15128

end BstLean.Part271.R3.Rows15110
