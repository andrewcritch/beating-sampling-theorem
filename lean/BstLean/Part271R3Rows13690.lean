import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13690–13764. -/
namespace BstLean.Part271.R3.Rows13690
open Real BstLean.Part130 BstLean.Part227

theorem width_13690 : mW 13690 = 300200954295536 := by
  have hu : mW 13690 ≤ 300200954295536 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13690 ≤ 300200954295535 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13690 : RowArithmetic 13690 (283483846568399384381/250000000000000000000000) (306462854771329971745369/500000000000000000000000) (7754284371955331/1000000000000000000000000) where
  r0 := (624302146007/1000000000000000000)
  k0 := (3735391942387901/1000000000000000000)
  k6 := (11703045997087009/1000000000000000000)
  q := (33093806066996887507/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13690]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13690]

theorem width_13691 : mW 13691 = 300277710999748 := by
  have hu : mW 13691 ≤ 300277710999748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13691 ≤ 300277710999747 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13691 : RowArithmetic 13691 (1133901498121345763161/1000000000000000000000000) (1532284541090514226881/2500000000000000000000) (7752808387802231/1000000000000000000000000) where
  r0 := (624233748073/1000000000000000000)
  k0 := (3735187313834683/1000000000000000000)
  k6 := (11702618590042071/1000000000000000000)
  q := (41368768412898153379/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13691]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13691]

theorem width_13692 : mW 13692 = 300354481721144 := by
  have hu : mW 13692 ≤ 300354481721144 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13692 ≤ 300354481721143 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13692 : RowArithmetic 13692 (70866726141704060907/62500000000000000000000) (612901925072560937703639/1000000000000000000000000) (3875666398142983/500000000000000000000000) where
  r0 := (624165362627/1000000000000000000)
  k0 := (746996542286869/200000000000000000)
  k6 := (11702191229821721/1000000000000000000)
  q := (6619244669900033239/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13692]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13692]

theorem width_13693 : mW 13693 = 300431266461262 := by
  have hu : mW 13693 ≤ 300431266461262 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13693 ≤ 300431266461261 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13693 : RowArithmetic 13693 (141729218338586772577/125000000000000000000000) (612890035451317827795931/1000000000000000000000000) (3874928798636201/500000000000000000000000) where
  r0 := (312048494833/500000000000000000)
  k0 := (373477813518221/100000000000000000)
  k6 := (11701763916417411/1000000000000000000)
  q := (165487159622733267819/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13693]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13693]

theorem width_13694 : mW 13694 = 300508065221637 := by
  have hu : mW 13694 ≤ 300508065221637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13694 ≤ 300508065221636 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13694 : RowArithmetic 13694 (1133799883442975480833/1000000000000000000000000) (76609768446508566815091/125000000000000000000000) (968547848828443/125000000000000000000000) where
  r0 := (156007157297/250000000000000000)
  k0 := (3734573585076589/1000000000000000000)
  k6 := (2340267329964119/200000000000000000)
  q := (8274660113865704877/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13694]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13694]

theorem width_13695 : mW 13695 = 300584878003804 := by
  have hu : mW 13695 ≤ 300584878003804 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13695 ≤ 300584878003803 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13695 : RowArithmetic 13695 (283441507116863015819/250000000000000000000000) (612866261434405447783579/1000000000000000000000000) (1936727094054363/250000000000000000000000) where
  r0 := (155990070297/250000000000000000)
  k0 := (29174758289897/7812500000000000)
  k6 := (5850454715011363/500000000000000000)
  q := (165499244711267489217/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13695]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13695]

theorem width_13696 : mW 13696 = 300661704809299 := by
  have hu : mW 13696 ≤ 300661704809299 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13696 ≤ 300661704809298 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13696 : RowArithmetic 13696 (226746436355893507789/200000000000000000000000) (38303398564870060034909/62500000000000000000000) (7745434353908217/1000000000000000000000000) where
  r0 := (9748311651/15625000000000000)
  k0 := (1867082281635601/500000000000000000)
  k6 := (11700482257015263/1000000000000000000)
  q := (41376321731154401879/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13696]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13696]

theorem width_13697 : mW 13697 = 300738545639659 := by
  have hu : mW 13697 ≤ 300738545639659 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13697 ≤ 300738545639658 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13697 : RowArithmetic 13697 (1133698343376365942559/1000000000000000000000000) (122568498876441557349749/200000000000000000000000) (7743960723565963/1000000000000000000000000) where
  r0 := (623823622613/1000000000000000000)
  k0 := (186698004578253/50000000000000000)
  k6 := (2340011026157933/200000000000000000)
  q := (33102265783477722539/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13697]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13697]

theorem width_13698 : mW 13698 = 300815400496420 := by
  have hu : mW 13698 ≤ 300815400496420 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13698 ≤ 300815400496419 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13698 : RowArithmetic 13698 (566832256627746531431/500000000000000000000000) (122566122693371724613841/200000000000000000000000) (60488183477007/7812500000000000000000) where
  r0 := (62375531203/100000000000000000)
  k0 := (93343891149443/25000000000000000)
  k6 := (5849814025668697/500000000000000000)
  q := (827586853448023303/5000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13698]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13698]

theorem width_13699 : mW 13699 = 300892269381117 := by
  have hu : mW 13699 ≤ 300892269381117 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13699 ≤ 300892269381116 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13699 : RowArithmetic 13699 (1133630691414196440627/1000000000000000000000000) (153204683572866580765949/250000000000000000000000) (7741014638247307/1000000000000000000000000) where
  r0 := (311843506957/500000000000000000)
  k0 := (3733551226510479/1000000000000000000)
  k6 := (5849600509324957/500000000000000000)
  q := (165523412241289902669/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13699]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13699]

theorem width_13700 : mW 13700 = 300969152295287 := by
  have hu : mW 13700 ≤ 300969152295287 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13700 ≤ 300969152295286 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13700 : RowArithmetic 13700 (566798438924911687087/500000000000000000000000) (38300428553476493835739/62500000000000000000000) (7739542183003489/1000000000000000000000000) where
  r0 := (623618728261/1000000000000000000)
  k0 := (1866673416577827/500000000000000000)
  k6 := (11698774032718691/1000000000000000000)
  q := (165529453572468485933/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13700]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13700]

theorem width_13701 : mW 13701 = 301046049240466 := by
  have hu : mW 13701 ≤ 301046049240466 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13701 ≤ 301046049240465 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13701 : RowArithmetic 13701 (1133563072559722913273/1000000000000000000000000) (612794981158924516450017/1000000000000000000000000) (386903505959591/50000000000000000000000) where
  r0 := (623550455067/1000000000000000000)
  k0 := (3733142465905561/1000000000000000000)
  k6 := (11698347093535193/1000000000000000000)
  q := (20691936835395569127/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13701]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13701]

theorem width_13702 : mW 13702 = 301122960218190 := by
  have hu : mW 13702 ≤ 301122960218190 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13702 ≤ 301122960218189 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13702 : RowArithmetic 13702 (1133529275541245193549/1000000000000000000000000) (612783107200961390804311/1000000000000000000000000) (483537402917421/62500000000000000000000) where
  r0 := (623482194331/1000000000000000000)
  k0 := (3732938124761493/1000000000000000000)
  k6 := (2924480050272723/250000000000000000)
  q := (20692691946675280267/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13702]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13702]

theorem width_13703 : mW 13703 = 301199885229996 := by
  have hu : mW 13703 ≤ 301199885229996 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13703 ≤ 301199885229995 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13703 : RowArithmetic 13703 (566747743395870386297/500000000000000000000000) (24510849399253120027251/40000000000000000000000) (7735127165330703/1000000000000000000000000) where
  r0 := (623413946047/1000000000000000000)
  k0 := (149309352388391/40000000000000000)
  k6 := (5848746677688629/500000000000000000)
  q := (16554757624320568711/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13703]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13703]

theorem width_13704 : mW 13704 = 301276824277420 := by
  have hu : mW 13704 ≤ 301276824277420 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13704 ≤ 301276824277419 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13704 : RowArithmetic 13704 (566730853154280978439/500000000000000000000000) (612759364499617745927723/1000000000000000000000000) (773365627501427/100000000000000000000000) where
  r0 := (311672855107/500000000000000000)
  k0 := (1866264760375849/500000000000000000)
  k6 := (1462133319548221/125000000000000000)
  q := (165553616692599017349/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13704]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13704]

theorem width_13705 : mW 13705 = 301353777361999 := by
  have hu : mW 13705 ≤ 301353777361999 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13705 ≤ 301353777361998 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13705 : RowArithmetic 13705 (1133427934089061474249/1000000000000000000000000) (612747495755424372940709/1000000000000000000000000) (7732185775596017/1000000000000000000000000) where
  r0 := (623277486827/1000000000000000000)
  k0 := (3732325257876577/1000000000000000000)
  k6 := (5848319902053949/500000000000000000)
  q := (20694957115200794733/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13705]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13705]

theorem width_13706 : mW 13706 = 301430744485268 := by
  have hu : mW 13706 ≤ 301430744485268 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13706 ≤ 301430744485267 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13706 : RowArithmetic 13706 (70837135633162153887/62500000000000000000000) (153183907187085409285641/250000000000000000000000) (966339458367829/125000000000000000000000) where
  r0 := (124641855177/200000000000000000)
  k0 := (1866060510542849/500000000000000000)
  k6 := (11696213098535127/1000000000000000000)
  q := (10347856058140739329/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13706]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13706]

theorem width_13707 : mW 13707 = 301507725648765 := by
  have hu : mW 13707 ≤ 301507725648765 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13707 ≤ 301507725648764 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13707 : RowArithmetic 13707 (226672082886103030697/200000000000000000000000) (76590470434745430420197/125000000000000000000000) (1545849189784157/200000000000000000000000) where
  r0 := (623141077383/1000000000000000000)
  k0 := (3731916810368373/1000000000000000000)
  k6 := (11695786439658937/1000000000000000000)
  q := (2069646708981994347/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13707]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13707]

theorem width_13708 : mW 13708 = 301584720854026 := by
  have hu : mW 13708 ≤ 301584720854026 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13708 ≤ 301584720854025 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13708 : RowArithmetic 13708 (1133326666986180189393/1000000000000000000000000) (612711899943883837483357/1000000000000000000000000) (1931944155349313/250000000000000000000000) where
  r0 := (623072891319/1000000000000000000)
  k0 := (1865856312861447/500000000000000000)
  k6 := (2923839956867703/250000000000000000)
  q := (82788888143276812581/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13708]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13708]

theorem width_13709 : mW 13709 = 301661730102587 := by
  have hu : mW 13709 ≤ 301661730102587 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13709 ≤ 301661730102586 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13709 : RowArithmetic 13709 (45331717111797891721/40000000000000000000000) (612700038145697019209111/1000000000000000000000000) (1931576921059717/250000000000000000000000) where
  r0 := (623004717689/1000000000000000000)
  k0 := (93287711678539/25000000000000000)
  k6 := (11694933261962237/1000000000000000000)
  q := (33116763126851633777/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13709]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13709]

theorem width_13710 : mW 13710 = 301738753395987 := by
  have hu : mW 13710 ≤ 301738753395987 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13710 ≤ 301738753395986 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13710 : RowArithmetic 13710 (1133259196854173284731/1000000000000000000000000) (30634408904149864967969/50000000000000000000000) (1544967827462489/200000000000000000000000) where
  r0 := (62293655649/100000000000000000)
  k0 := (746260866923933/200000000000000000)
  k6 := (116945067431247/10000000000000000)
  q := (41397463690424320487/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13710]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13710]

theorem width_13711 : mW 13711 = 301815790735760 := by
  have hu : mW 13711 ≤ 301815790735760 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13711 ≤ 301815790735759 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13711 : RowArithmetic 13711 (1133225474161219374253/1000000000000000000000000) (122535263951075811672589/200000000000000000000000) (7723370980484983/1000000000000000000000000) where
  r0 := (622868407719/1000000000000000000)
  k0 := (1865550114076251/500000000000000000)
  k6 := (11694080270949691/1000000000000000000)
  q := (165595893668895062973/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13711]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13711]

theorem width_13712 : mW 13712 = 301892842123444 := by
  have hu : mW 13712 ≤ 301892842123444 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13712 ≤ 301892842123443 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13712 : RowArithmetic 13712 (566595879856722603043/500000000000000000000000) (153166115790609236634983/250000000000000000000000) (3860951606811717/500000000000000000000000) where
  r0 := (622800271373/1000000000000000000)
  k0 := (3730896147735361/1000000000000000000)
  k6 := (5846826922714351/500000000000000000)
  q := (16560193235587560619/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13712]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13712]

theorem width_13713 : mW 13713 = 301969907560577 := by
  have hu : mW 13713 ≤ 301969907560577 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13713 ≤ 301969907560576 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13713 : RowArithmetic 13713 (113315805350821150653/100000000000000000000000) (38290788018985346472529/62500000000000000000000) (7720435836594809/1000000000000000000000000) where
  r0 := (622732147449/1000000000000000000)
  k0 := (3730692093363529/1000000000000000000)
  k6 := (2923306866638307/250000000000000000)
  q := (33121594164532600287/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13713]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13713]

theorem width_13714 : mW 13714 = 302046987048694 := by
  have hu : mW 13714 ≤ 302046987048694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13714 ≤ 302046987048693 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13714 : RowArithmetic 13714 (226624871108576412757/200000000000000000000000) (306320377589479894971419/500000000000000000000000) (6175175079413/800000000000000000000) where
  r0 := (622664035943/1000000000000000000)
  k0 := (37304880650293/10000000000000000)
  k6 := (2338560226862953/200000000000000000)
  q := (165614009069281334151/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13714]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13714]

theorem width_13715 : mW 13715 = 302124080589333 := by
  have hu : mW 13715 ≤ 302124080589333 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13715 ≤ 302124080589332 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13715 : RowArithmetic 13715 (283272666453704940881/250000000000000000000000) (61262890378761453785793/100000000000000000000000) (3858751125752441/500000000000000000000000) where
  r0 := (155648984213/250000000000000000)
  k0 := (1865142031363979/500000000000000000)
  k6 := (2923093712176203/250000000000000000)
  q := (82810023547877342697/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13715]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13715]

theorem width_13716 : mW 13716 = 302201188184031 := by
  have hu : mW 13716 ≤ 302201188184031 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13716 ≤ 302201188184030 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13716 : RowArithmetic 13716 (45322279372855569247/40000000000000000000000) (612617054129324968721967/1000000000000000000000000) (771603604317791/100000000000000000000000) where
  r0 := (311263925087/500000000000000000)
  k0 := (3730080086457783/1000000000000000000)
  k6 := (1169194860971487/100000000000000000)
  q := (41406521225526782957/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13716]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13716]

theorem width_13717 : mW 13717 = 302278309834326 := by
  have hu : mW 13717 ≤ 302278309834326 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13717 ≤ 302278309834325 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13717 : RowArithmetic 13717 (226604662211991102237/200000000000000000000000) (30630260310184311321857/50000000000000000000000) (771457022415257/100000000000000000000000) where
  r0 := (19451867997/31250000000000000)
  k0 := (745975227241613/200000000000000000)
  k6 := (5845761208668221/500000000000000000)
  q := (165632122488362745729/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13717]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13717]

theorem width_13718 : mW 13718 = 302355445541753 := by
  have hu : mW 13718 ≤ 302355445541753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13718 ≤ 302355445541752 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13718 : RowArithmetic 13718 (1132989646027886704251/1000000000000000000000000) (61259336001029365631463/100000000000000000000000) (7713104794296233/1000000000000000000000000) where
  r0 := (15559792851/25000000000000000)
  k0 := (93241805299427/25000000000000000)
  k6 := (5845548135780517/500000000000000000)
  q := (82819079927272797493/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13718]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13718]

theorem width_13719 : mW 13719 = 302432595307851 := by
  have hu : mW 13719 ≤ 302432595307851 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13719 ≤ 302432595307850 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13719 : RowArithmetic 13719 (1132955989222549350813/1000000000000000000000000) (612581515548742770458517/1000000000000000000000000) (60247185574033/7812500000000000000000) where
  r0 := (622323664579/1000000000000000000)
  k0 := (3729468313760107/1000000000000000000)
  k6 := (1461333771547519/125000000000000000)
  q := (165644197000679743101/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13719]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13719]

theorem width_13720 : mW 13720 = 302509759134157 := by
  have hu : mW 13720 ≤ 302509759134157 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13720 ≤ 302509759134156 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13720 : RowArithmetic 13720 (566461170320656193661/500000000000000000000000) (19142802275582160880663/31250000000000000000000) (3855087550779987/500000000000000000000000) where
  r0 := (622255627517/1000000000000000000)
  k0 := (1864632220774713/500000000000000000)
  k6 := (11690244119785307/1000000000000000000)
  q := (20706279240848656149/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13720]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13720]

theorem width_13721 : mW 13721 = 302586937022208 := by
  have hu : mW 13721 ≤ 302586937022208 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13721 ≤ 302586937022207 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13721 : RowArithmetic 13721 (1132888700281545826353/1000000000000000000000000) (306278915909774262959769/500000000000000000000000) (1927177709603743/250000000000000000000000) where
  r0 := (155546900713/250000000000000000)
  k0 := (372906059534331/100000000000000000)
  k6 := (11689818113768009/1000000000000000000)
  q := (33131254126579633599/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13721]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13721]

theorem width_13722 : mW 13722 = 302664128973541 := by
  have hu : mW 13722 ≤ 302664128973541 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13722 ≤ 302664128973540 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13722 : RowArithmetic 13722 (566427534070310378017/500000000000000000000000) (612545992551096763745569/1000000000000000000000000) (7707246963908763/1000000000000000000000000) where
  r0 := (31105979529/50000000000000000)
  k0 := (932214193783509/250000000000000000)
  k6 := (5844696077159887/500000000000000000)
  q := (82831153559515274929/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13722]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13722]

theorem width_13723 : mW 13723 = 302741334989694 := by
  have hu : mW 13723 ≤ 302741334989694 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13723 ≤ 302741334989693 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13723 : RowArithmetic 13723 (1132821444215908681783/1000000000000000000000000) (61253415501286985241271/100000000000000000000000) (1926445869477231/250000000000000000000000) where
  r0 := (622051590697/1000000000000000000)
  k0 := (3728652980913879/1000000000000000000)
  k6 := (11688966241432117/1000000000000000000)
  q := (165668343385210440753/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13723]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13723]

theorem width_13724 : mW 13724 = 302818555072204 := by
  have hu : mW 13724 ≤ 302818555072204 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13724 ≤ 302818555072203 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13724 : RowArithmetic 13724 (1132787828504782841971/1000000000000000000000000) (1196332654696218549523/1953125000000000000000) (3852160190141557/500000000000000000000000) where
  r0 := (310991801601/500000000000000000)
  k0 := (1864224606342051/500000000000000000)
  k6 := (2337708075019311/200000000000000000)
  q := (41418594857865470567/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13724]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13724]

theorem width_13725 : mW 13725 = 302895789222610 := by
  have hu : mW 13725 ≤ 302895789222610 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13725 ≤ 302895789222609 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13725 : RowArithmetic 13725 (1132754221004616234541/1000000000000000000000000) (153127621281368788402277/250000000000000000000000) (1540571534179799/200000000000000000000000) where
  r0 := (62191562809/100000000000000000)
  k0 := (1864122735216991/500000000000000000)
  k6 := (11688114555304611/1000000000000000000)
  q := (82840207628904455807/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13725]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13725]

theorem width_13726 : mW 13726 = 302973037442448 := by
  have hu : mW 13726 ≤ 302973037442448 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13726 ≤ 302973037442447 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13726 : RowArithmetic 13726 (1132720621712784903541/1000000000000000000000000) (153124663193875004352367/250000000000000000000000) (1925348837406091/250000000000000000000000) where
  r0 := (310923832679/500000000000000000)
  k0 := (58250652408731/15625000000000000)
  k6 := (5843844391023903/500000000000000000)
  q := (8284322543213778081/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13726]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13726]

theorem width_13727 : mW 13727 = 303050299733256 := by
  have hu : mW 13727 ≤ 303050299733256 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13727 ≤ 303050299733255 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13727 : RowArithmetic 13727 (283171757656666162863/250000000000000000000000) (612486822154134947952331/1000000000000000000000000) (481245838520439/62500000000000000000000) where
  r0 := (155444928751/250000000000000000)
  k0 := (931959515964193/250000000000000000)
  k6 := (2337452611063533/200000000000000000)
  q := (82846243125442930371/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13727]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13727]

theorem width_13728 : mW 13728 = 303127576096573 := by
  have hu : mW 13728 ≤ 303127576096573 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13728 ≤ 303127576096572 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13728 : RowArithmetic 13728 (566326723871815848859/500000000000000000000000) (612474993260976636821929/1000000000000000000000000) (962308983859351/125000000000000000000000) where
  r0 := (24868471081/40000000000000000)
  k0 := (3727634399523209/1000000000000000000)
  k6 := (2337367475021143/200000000000000000)
  q := (82849260708831916529/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13728]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13728]

theorem width_13729 : mW 13729 = 303204866533935 := by
  have hu : mW 13729 ≤ 303204866533935 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13729 ≤ 303204866533934 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13729 : RowArithmetic 13729 (1132619873061065303677/1000000000000000000000000) (612463166095621861592223/1000000000000000000000000) (7697010713135681/1000000000000000000000000) where
  r0 := (77705481427/125000000000000000)
  k0 := (1863715380573681/500000000000000000)
  k6 := (2337282348280697/200000000000000000)
  q := (16570455636463349827/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13729]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13729]

theorem width_13730 : mW 13730 = 303282171046880 := by
  have hu : mW 13730 ≤ 303282171046880 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13730 ≤ 303282171046879 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13730 : RowArithmetic 13730 (283146576644086122269/250000000000000000000000) (382782087911042134817/625000000000000000000) (3847774971488807/500000000000000000000000) where
  r0 := (24863037527/40000000000000000)
  k0 := (372722714872749/100000000000000000)
  k6 := (5842993077101253/500000000000000000)
  q := (165710591091818871709/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13730]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13730]

theorem width_13731 : mW 13731 = 303359489636948 := by
  have hu : mW 13731 ≤ 303359489636948 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13731 ≤ 303359489636947 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13731 : RowArithmetic 13731 (283138187071712008573/250000000000000000000000) (306219758473355209097477/500000000000000000000000) (961761195033573/125000000000000000000000) where
  r0 := (621508037299/1000000000000000000)
  k0 := (3727023562258851/1000000000000000000)
  k6 := (1460695076686789/125000000000000000)
  q := (165716625599243964331/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13731]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13731]

theorem width_13732 : mW 13732 = 303436822305674 := by
  have hu : mW 13732 ≤ 303436822305674 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13732 ≤ 303436822305673 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13732 : RowArithmetic 13732 (141564899773744883611/125000000000000000000000) (61242769496234800155027/100000000000000000000000) (7692629564876751/1000000000000000000000000) where
  r0 := (38840009299/62500000000000000)
  k0 := (465852500216713/125000000000000000)
  k6 := (5842567559635219/500000000000000000)
  q := (165722659886932782721/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13732]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13732]

theorem width_13733 : mW 13733 = 303514169054598 := by
  have hu : mW 13733 ≤ 303514169054598 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13733 ≤ 303514169054597 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13733 : RowArithmetic 13733 (1132485656283058514959/1000000000000000000000000) (612415874704177408463231/1000000000000000000000000) (1922792489167551/250000000000000000000000) where
  r0 := (155343068157/250000000000000000)
  k0 := (3726616467150303/1000000000000000000)
  k6 := (5842354835761211/500000000000000000)
  q := (165728693954909329093/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13733]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13733]

theorem width_13734 : mW 13734 = 303591529885258 := by
  have hu : mW 13734 ≤ 303591529885258 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13734 ≤ 303591529885257 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13734 : RowArithmetic 13734 (566226061281764837983/500000000000000000000000) (153101014042949020344587/250000000000000000000000) (3844855367758569/500000000000000000000000) where
  r0 := (621304408827/1000000000000000000)
  k0 := (3726412958500903/1000000000000000000)
  k6 := (11684284270241803/1000000000000000000)
  q := (82867363901598800647/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13734]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13734]

theorem width_13735 : mW 13735 = 303668904799191 := by
  have hu : mW 13735 ≤ 303668904799191 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13735 ≤ 303668904799190 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13735 : RowArithmetic 13735 (1132418597028757579039/1000000000000000000000000) (76549029920600193825603/125000000000000000000000) (7688251901285833/1000000000000000000000000) where
  r0 := (310618278689/500000000000000000)
  k0 := (3726209475780757/1000000000000000000)
  k6 := (2920964728855031/250000000000000000)
  q := (207175951789776991/1250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13735]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13735]

theorem width_13736 : mW 13736 = 303746293797936 := by
  have hu : mW 13736 ≤ 303746293797936 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13736 ≤ 303746293797935 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13736 : RowArithmetic 13736 (1132385079676127010777/1000000000000000000000000) (612380424282791461826103/1000000000000000000000000) (768679345384457/100000000000000000000000) where
  r0 := (310584359139/500000000000000000)
  k0 := (745201203797023/200000000000000000)
  k6 := (11683433607048929/1000000000000000000)
  q := (2071834935510066159/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13736]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13736]

theorem width_13737 : mW 13737 = 303823696883031 := by
  have hu : mW 13737 ≤ 303823696883031 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13737 ≤ 303823696883030 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13737 : RowArithmetic 13737 (1132351570503024480873/1000000000000000000000000) (306184305462681828415821/500000000000000000000000) (1537067078612343/200000000000000000000000) where
  r0 := (155275222881/250000000000000000)
  k0 := (1862901294054613/500000000000000000)
  k6 := (11683008345119763/1000000000000000000)
  q := (828764140150863429/5000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13737]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13737]

theorem width_13738 : mW 13738 = 303901114056015 := by
  have hu : mW 13738 ≤ 303901114056015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13738 ≤ 303901114056014 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13738 : RowArithmetic 13738 (1132318069506836913113/1000000000000000000000000) (153089199823029001641831/250000000000000000000000) (3841938859402831/500000000000000000000000) where
  r0 := (621033077113/1000000000000000000)
  k0 := (3725599183148337/1000000000000000000)
  k6 := (11682583129624177/1000000000000000000)
  q := (165758860999947752417/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13738]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13738]

theorem width_13739 : mW 13739 = 303978545318425 := by
  have hu : mW 13739 ≤ 303978545318425 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13739 ≤ 303978545318424 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13739 : RowArithmetic 13739 (70767786042809600371/62500000000000000000000) (489875991506117275369/800000000000000000000) (3841210215472457/500000000000000000000000) where
  r0 := (620965275041/1000000000000000000)
  k0 := (1862697902047347/500000000000000000)
  k6 := (11682157960553719/1000000000000000000)
  q := (165764893750154468587/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13739]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13739]

theorem width_13740 : mW 13740 = 304055990671800 := by
  have hu : mW 13740 ≤ 304055990671800 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13740 ≤ 304055990671799 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13740 : RowArithmetic 13740 (566125546017381808613/500000000000000000000000) (76541647649569197657413/125000000000000000000000) (7680963529347979/1000000000000000000000000) where
  r0 := (124179497061/200000000000000000)
  k0 := (1862596225471771/500000000000000000)
  k6 := (1460216604737493/125000000000000000)
  q := (82885463140408402981/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13740]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13740]

theorem width_13741 : mW 13741 = 304133450117679 := by
  have hu : mW 13741 ≤ 304133450117679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13741 ≤ 304133450117678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13741 : RowArithmetic 13741 (1132217615553657071899/1000000000000000000000000) (12246427494668706322783/20000000000000000000000) (7679507013883419/1000000000000000000000000) where
  r0 := (620829707903/1000000000000000000)
  k0 := (1862494561846561/500000000000000000)
  k6 := (5840653880827203/500000000000000000)
  q := (165776958591958731833/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13741]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13741]

theorem width_13742 : mW 13742 = 304210923657600 := by
  have hu : mW 13742 ≤ 304210923657600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13742 ≤ 304210923657599 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13742 : RowArithmetic 13742 (1132184147239025813763/1000000000000000000000000) (306154784996445083236869/500000000000000000000000) (7678050884419879/1000000000000000000000000) where
  r0 := (620761942831/1000000000000000000)
  k0 := (148991432893427/40000000000000000)
  k6 := (11680882731808661/1000000000000000000)
  q := (41445747670901052283/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13742]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13742]

theorem width_13743 : mW 13743 = 304288411293101 := by
  have hu : mW 13743 ≤ 304288411293101 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13743 ≤ 304288411293100 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13743 : RowArithmetic 13743 (1132150687088262751427/1000000000000000000000000) (76537220871814595765867/125000000000000000000000) (7676595140826061/1000000000000000000000000) where
  r0 := (310347095043/500000000000000000)
  k0 := (3724582546866441/1000000000000000000)
  k6 := (1168045774835427/100000000000000000)
  q := (41447255638944299107/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13743]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13743]

theorem width_13744 : mW 13744 = 304365913025722 := by
  have hu : mW 13744 ≤ 304365913025722 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13744 ≤ 304365913025721 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13744 : RowArithmetic 13744 (35378663596836267313/31250000000000000000000) (612285965677913814698683/1000000000000000000000000) (7675139782970669/1000000000000000000000000) where
  r0 := (124125289933/200000000000000000)
  k0 := (232773706080041/62500000000000000)
  k6 := (11680032811282793/1000000000000000000)
  q := (82897527104250823967/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13744]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13744]

theorem width_13745 : mW 13745 = 304443428857000 := by
  have hu : mW 13745 ≤ 304443428857000 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13745 ≤ 304443428856999 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13745 : RowArithmetic 13745 (113208379126791491131/100000000000000000000000) (38267135381417502549991/62500000000000000000000) (7673684810722543/1000000000000000000000000) where
  r0 := (155139680391/250000000000000000)
  k0 := (931044018392639/250000000000000000)
  k6 := (5839803960292897/500000000000000000)
  q := (165801085641801513507/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13745]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13745]

theorem width_13746 : mW 13746 = 304520958788475 := by
  have hu : mW 13746 ≤ 304520958788475 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13746 ≤ 304520958788474 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13746 : RowArithmetic 13746 (113205035559312062117/100000000000000000000000) (306131184124207236954399/500000000000000000000000) (15344460447901/2000000000000000000000) where
  r0 := (620491005781/1000000000000000000)
  k0 := (238334264047/64000000000000)
  k6 := (11679183076254839/1000000000000000000)
  q := (82903558427850369323/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13746]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13746]

theorem width_13747 : mW 13747 = 304598502821686 := by
  have hu : mW 13747 ≤ 304598502821686 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13747 ≤ 304598502821685 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13747 : RowArithmetic 13747 (56600846403588709863/50000000000000000000000) (612250572114716177628841/1000000000000000000000000) (7670776022523439/1000000000000000000000000) where
  r0 := (620423302313/1000000000000000000)
  k0 := (3723769703767347/1000000000000000000)
  k6 := (1459844784785187/125000000000000000)
  q := (10363321740638954031/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13747]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13747]

theorem width_13748 : mW 13748 = 304676060958171 := by
  have hu : mW 13748 ≤ 304676060958171 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13748 ≤ 304676060958170 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13748 : RowArithmetic 13748 (1131983508701273867107/1000000000000000000000000) (61223877770118433793109/100000000000000000000000) (7669322206310339/1000000000000000000000000) where
  r0 := (124071122231/200000000000000000)
  k0 := (3723566557658699/1000000000000000000)
  k6 := (5839166763328667/500000000000000000)
  q := (165819178625393027847/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13748]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13748]

theorem width_13749 : mW 13749 = 304753633199469 := by
  have hu : mW 13749 ≤ 304753633199469 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13749 ≤ 304753633199468 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13749 : RowArithmetic 13749 (1131950097479018269193/1000000000000000000000000) (122445397001483656926857/200000000000000000000000) (7667868775180213/1000000000000000000000000) where
  r0 := (310143966153/500000000000000000)
  k0 := (3723363437409663/1000000000000000000)
  k6 := (467116352854957/40000000000000000)
  q := (82912604590616980569/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13749]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13749]

theorem width_13750 : mW 13750 = 304831219547119 := by
  have hu : mW 13750 ≤ 304831219547119 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13750 ≤ 304831219547118 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13750 : RowArithmetic 13750 (1131916694402407103983/1000000000000000000000000) (612215194033017533941273/1000000000000000000000000) (61331325832017/8000000000000000000000) where
  r0 := (310110132881/500000000000000000)
  k0 := (1861580171506233/500000000000000000)
  k6 := (2335496832484569/200000000000000000)
  q := (20728904939721249057/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13750]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13750]

theorem width_13751 : mW 13751 = 304908820002660 := by
  have hu : mW 13751 ≤ 304908820002660 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13751 ≤ 304908820002659 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13751 : RowArithmetic 13751 (1131883299468841133367/1000000000000000000000000) (306101702388790808303021/500000000000000000000000) (7664963067645199/1000000000000000000000000) where
  r0 := (1937976911/3125000000000000)
  k0 := (3722957274462333/1000000000000000000)
  k6 := (11677059549795669/1000000000000000000)
  q := (165837269635025045537/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13751]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13751]

theorem width_13752 : mW 13752 = 304986434567632 := by
  have hu : mW 13752 ≤ 304986434567632 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13752 ≤ 304986434567631 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13752 : RowArithmetic 13752 (565924956337860765221/500000000000000000000000) (76523952155088784579807/125000000000000000000000) (7663510790978587/1000000000000000000000000) where
  r0 := (620084969577/1000000000000000000)
  k0 := (3722754231754489/1000000000000000000)
  k6 := (1459579372935497/125000000000000000)
  q := (165843299533023039767/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13752]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13752]

theorem width_13753 : mW 13753 = 305064063243573 := by
  have hu : mW 13753 ≤ 305064063243573 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13753 ≤ 305064063243572 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13753 : RowArithmetic 13753 (113181653402045182847/100000000000000000000000) (61217983142200335706479/100000000000000000000000) (7662058898871547/1000000000000000000000000) where
  r0 := (620017339929/1000000000000000000)
  k0 := (1861275607440577/500000000000000000)
  k6 := (5838105231739673/500000000000000000)
  q := (82924664605893945093/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13753]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13753]

theorem width_13754 : mW 13754 = 305141706032022 := by
  have hu : mW 13754 ≤ 305141706032022 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13754 ≤ 305141706032021 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13754 : RowArithmetic 13754 (70736447718777248141/62500000000000000000000) (24486721892842432443931/40000000000000000000000) (7660607391193369/1000000000000000000000000) where
  r0 := (619949722573/1000000000000000000)
  k0 := (3722348223837549/1000000000000000000)
  k6 := (11675785989773363/1000000000000000000)
  q := (41463839667835876871/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13754]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13754]

theorem width_13755 : mW 13755 = 305219362934519 := by
  have hu : mW 13755 ≤ 305219362934519 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13755 ≤ 305219362934518 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13755 : RowArithmetic 13755 (7073436256956739431/6250000000000000000000) (24486250597499311111259/40000000000000000000000) (1914789066953343/250000000000000000000000) where
  r0 := (154970529377/250000000000000000)
  k0 := (3722145258624897/1000000000000000000)
  k6 := (11675361562357611/1000000000000000000)
  q := (165861387911713798007/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13755]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13755]

theorem width_13756 : mW 13756 = 305297033952604 := by
  have hu : mW 13756 ≤ 305297033952604 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13756 ≤ 305297033952603 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13756 : RowArithmetic 13756 (1131716446855784257471/1000000000000000000000000) (306072242135434709499493/500000000000000000000000) (1914426382150233/250000000000000000000000) where
  r0 := (77476815591/125000000000000000)
  k0 := (3721942319229411/1000000000000000000)
  k6 := (11674937181223677/1000000000000000000)
  q := (33173483386584532751/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13756]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13756]

theorem width_13757 : mW 13757 = 305374719087815 := by
  have hu : mW 13757 ≤ 305374719087815 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13757 ≤ 305374719087814 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13757 : RowArithmetic 13757 (1131683100725961584413/1000000000000000000000000) (122426541064164238491001/200000000000000000000000) (765625517342553/100000000000000000000000) where
  r0 := (619746944231/1000000000000000000)
  k0 := (3721739405649307/1000000000000000000)
  k6 := (11674512846363151/1000000000000000000)
  q := (33174689146998800477/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13757]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13757]

theorem width_13758 : mW 13758 = 305452418341691 := by
  have hu : mW 13758 ≤ 305452418341691 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13758 ≤ 305452418341690 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13758 : RowArithmetic 13758 (226329952544203693363/200000000000000000000000) (61212092808693846730887/100000000000000000000000) (3827402601078339/500000000000000000000000) where
  r0 := (123935875203/200000000000000000)
  k0 := (1860768258941401/500000000000000000)
  k6 := (1459261069720953/125000000000000000)
  q := (165879474317951707211/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13758]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13758]

theorem width_13759 : mW 13759 = 305530131715773 := by
  have hu : mW 13759 ≤ 305530131715773 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13759 ≤ 305530131715772 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13759 : RowArithmetic 13759 (282904108209590710801/250000000000000000000000) (612109152568821949048957/1000000000000000000000000) (1913338903665973/250000000000000000000000) where
  r0 := (24784472803/40000000000000000)
  k0 := (744266731183821/200000000000000000)
  k6 := (1167366431542869/100000000000000000)
  q := (41471375670454916801/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13759]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13759]

theorem width_13760 : mW 13760 = 305607859211600 := by
  have hu : mW 13760 ≤ 305607859211600 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13760 ≤ 305607859211599 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13760 : RowArithmetic 13760 (70723944442212812851/62500000000000000000000) (306048689383036154031473/500000000000000000000000) (3825953205408397/500000000000000000000000) where
  r0 := (619544276409/1000000000000000000)
  k0 := (3721130819756429/1000000000000000000)
  k6 := (1459155014917243/125000000000000000)
  q := (165891530826621766997/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13760]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13760]

theorem width_13761 : mW 13761 = 305685600830711 := by
  have hu : mW 13761 ≤ 305685600830711 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13761 ≤ 305685600830710 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13761 : RowArithmetic 13761 (1131549797429556301931/1000000000000000000000000) (153021401669572613045677/250000000000000000000000) (956307198810633/125000000000000000000000) where
  r0 := (309738372507/500000000000000000)
  k0 := (3720928009389983/1000000000000000000)
  k6 := (1459101996185873/125000000000000000)
  q := (165897558752381886881/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13761]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13761]

theorem width_13762 : mW 13762 = 305763356574646 := by
  have hu : mW 13762 ≤ 305763356574646 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13762 ≤ 305763356574645 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13762 : RowArithmetic 13762 (1131516491898228488407/1000000000000000000000000) (153018459076269325736097/250000000000000000000000) (7649009153538409/1000000000000000000000000) where
  r0 := (309704612943/500000000000000000)
  k0 := (3720725224811973/1000000000000000000)
  k6 := (11672391865867411/1000000000000000000)
  q := (165903586459123902811/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13762]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13762]

theorem width_13763 : mW 13763 = 305841126444944 := by
  have hu : mW 13763 ≤ 305841126444944 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13763 ≤ 305841126444943 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13763 : RowArithmetic 13763 (1131483194478835023767/1000000000000000000000000) (38253879227877129712051/62500000000000000000000) (3823780549923309/500000000000000000000000) where
  r0 := (309670859511/500000000000000000)
  k0 := (3720522466017603/1000000000000000000)
  k6 := (466878712338833/40000000000000000)
  q := (165909613946871686403/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13763]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13763]

theorem width_13764 : mW 13764 = 305918910443147 := by
  have hu : mW 13764 ≤ 305918910443147 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13764 ≤ 305918910443146 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13764 : RowArithmetic 13764 (282862476292197120457/250000000000000000000000) (612050300700761990115653/1000000000000000000000000) (382305671463973/50000000000000000000000) where
  r0 := (30963711221/50000000000000000)
  k0 := (1860159866502541/500000000000000000)
  k6 := (91183935916319/7812500000000000)
  q := (82957820607824552469/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13764]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13764]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13690 then ⟨(283483846568399384381/250000000000000000000000), (306462854771329971745369/500000000000000000000000), (7754284371955331/1000000000000000000000000)⟩ else
  if n = 13691 then ⟨(1133901498121345763161/1000000000000000000000000), (1532284541090514226881/2500000000000000000000), (7752808387802231/1000000000000000000000000)⟩ else
  if n = 13692 then ⟨(70866726141704060907/62500000000000000000000), (612901925072560937703639/1000000000000000000000000), (3875666398142983/500000000000000000000000)⟩ else
  if n = 13693 then ⟨(141729218338586772577/125000000000000000000000), (612890035451317827795931/1000000000000000000000000), (3874928798636201/500000000000000000000000)⟩ else
  if n = 13694 then ⟨(1133799883442975480833/1000000000000000000000000), (76609768446508566815091/125000000000000000000000), (968547848828443/125000000000000000000000)⟩ else
  if n = 13695 then ⟨(283441507116863015819/250000000000000000000000), (612866261434405447783579/1000000000000000000000000), (1936727094054363/250000000000000000000000)⟩ else
  if n = 13696 then ⟨(226746436355893507789/200000000000000000000000), (38303398564870060034909/62500000000000000000000), (7745434353908217/1000000000000000000000000)⟩ else
  if n = 13697 then ⟨(1133698343376365942559/1000000000000000000000000), (122568498876441557349749/200000000000000000000000), (7743960723565963/1000000000000000000000000)⟩ else
  if n = 13698 then ⟨(566832256627746531431/500000000000000000000000), (122566122693371724613841/200000000000000000000000), (60488183477007/7812500000000000000000)⟩ else
  if n = 13699 then ⟨(1133630691414196440627/1000000000000000000000000), (153204683572866580765949/250000000000000000000000), (7741014638247307/1000000000000000000000000)⟩ else
  if n = 13700 then ⟨(566798438924911687087/500000000000000000000000), (38300428553476493835739/62500000000000000000000), (7739542183003489/1000000000000000000000000)⟩ else
  if n = 13701 then ⟨(1133563072559722913273/1000000000000000000000000), (612794981158924516450017/1000000000000000000000000), (386903505959591/50000000000000000000000)⟩ else
  if n = 13702 then ⟨(1133529275541245193549/1000000000000000000000000), (612783107200961390804311/1000000000000000000000000), (483537402917421/62500000000000000000000)⟩ else
  if n = 13703 then ⟨(566747743395870386297/500000000000000000000000), (24510849399253120027251/40000000000000000000000), (7735127165330703/1000000000000000000000000)⟩ else
  if n = 13704 then ⟨(566730853154280978439/500000000000000000000000), (612759364499617745927723/1000000000000000000000000), (773365627501427/100000000000000000000000)⟩ else
  if n = 13705 then ⟨(1133427934089061474249/1000000000000000000000000), (612747495755424372940709/1000000000000000000000000), (7732185775596017/1000000000000000000000000)⟩ else
  if n = 13706 then ⟨(70837135633162153887/62500000000000000000000), (153183907187085409285641/250000000000000000000000), (966339458367829/125000000000000000000000)⟩ else
  if n = 13707 then ⟨(226672082886103030697/200000000000000000000000), (76590470434745430420197/125000000000000000000000), (1545849189784157/200000000000000000000000)⟩ else
  if n = 13708 then ⟨(1133326666986180189393/1000000000000000000000000), (612711899943883837483357/1000000000000000000000000), (1931944155349313/250000000000000000000000)⟩ else
  if n = 13709 then ⟨(45331717111797891721/40000000000000000000000), (612700038145697019209111/1000000000000000000000000), (1931576921059717/250000000000000000000000)⟩ else
  if n = 13710 then ⟨(1133259196854173284731/1000000000000000000000000), (30634408904149864967969/50000000000000000000000), (1544967827462489/200000000000000000000000)⟩ else
  if n = 13711 then ⟨(1133225474161219374253/1000000000000000000000000), (122535263951075811672589/200000000000000000000000), (7723370980484983/1000000000000000000000000)⟩ else
  if n = 13712 then ⟨(566595879856722603043/500000000000000000000000), (153166115790609236634983/250000000000000000000000), (3860951606811717/500000000000000000000000)⟩ else
  if n = 13713 then ⟨(113315805350821150653/100000000000000000000000), (38290788018985346472529/62500000000000000000000), (7720435836594809/1000000000000000000000000)⟩ else
  if n = 13714 then ⟨(226624871108576412757/200000000000000000000000), (306320377589479894971419/500000000000000000000000), (6175175079413/800000000000000000000)⟩ else
  if n = 13715 then ⟨(283272666453704940881/250000000000000000000000), (61262890378761453785793/100000000000000000000000), (3858751125752441/500000000000000000000000)⟩ else
  if n = 13716 then ⟨(45322279372855569247/40000000000000000000000), (612617054129324968721967/1000000000000000000000000), (771603604317791/100000000000000000000000)⟩ else
  if n = 13717 then ⟨(226604662211991102237/200000000000000000000000), (30630260310184311321857/50000000000000000000000), (771457022415257/100000000000000000000000)⟩ else
  if n = 13718 then ⟨(1132989646027886704251/1000000000000000000000000), (61259336001029365631463/100000000000000000000000), (7713104794296233/1000000000000000000000000)⟩ else
  if n = 13719 then ⟨(1132955989222549350813/1000000000000000000000000), (612581515548742770458517/1000000000000000000000000), (60247185574033/7812500000000000000000)⟩ else
  if n = 13720 then ⟨(566461170320656193661/500000000000000000000000), (19142802275582160880663/31250000000000000000000), (3855087550779987/500000000000000000000000)⟩ else
  if n = 13721 then ⟨(1132888700281545826353/1000000000000000000000000), (306278915909774262959769/500000000000000000000000), (1927177709603743/250000000000000000000000)⟩ else
  if n = 13722 then ⟨(566427534070310378017/500000000000000000000000), (612545992551096763745569/1000000000000000000000000), (7707246963908763/1000000000000000000000000)⟩ else
  if n = 13723 then ⟨(1132821444215908681783/1000000000000000000000000), (61253415501286985241271/100000000000000000000000), (1926445869477231/250000000000000000000000)⟩ else
  if n = 13724 then ⟨(1132787828504782841971/1000000000000000000000000), (1196332654696218549523/1953125000000000000000), (3852160190141557/500000000000000000000000)⟩ else
  if n = 13725 then ⟨(1132754221004616234541/1000000000000000000000000), (153127621281368788402277/250000000000000000000000), (1540571534179799/200000000000000000000000)⟩ else
  if n = 13726 then ⟨(1132720621712784903541/1000000000000000000000000), (153124663193875004352367/250000000000000000000000), (1925348837406091/250000000000000000000000)⟩ else
  if n = 13727 then ⟨(283171757656666162863/250000000000000000000000), (612486822154134947952331/1000000000000000000000000), (481245838520439/62500000000000000000000)⟩ else
  if n = 13728 then ⟨(566326723871815848859/500000000000000000000000), (612474993260976636821929/1000000000000000000000000), (962308983859351/125000000000000000000000)⟩ else
  if n = 13729 then ⟨(1132619873061065303677/1000000000000000000000000), (612463166095621861592223/1000000000000000000000000), (7697010713135681/1000000000000000000000000)⟩ else
  if n = 13730 then ⟨(283146576644086122269/250000000000000000000000), (382782087911042134817/625000000000000000000), (3847774971488807/500000000000000000000000)⟩ else
  if n = 13731 then ⟨(283138187071712008573/250000000000000000000000), (306219758473355209097477/500000000000000000000000), (961761195033573/125000000000000000000000)⟩ else
  if n = 13732 then ⟨(141564899773744883611/125000000000000000000000), (61242769496234800155027/100000000000000000000000), (7692629564876751/1000000000000000000000000)⟩ else
  if n = 13733 then ⟨(1132485656283058514959/1000000000000000000000000), (612415874704177408463231/1000000000000000000000000), (1922792489167551/250000000000000000000000)⟩ else
  if n = 13734 then ⟨(566226061281764837983/500000000000000000000000), (153101014042949020344587/250000000000000000000000), (3844855367758569/500000000000000000000000)⟩ else
  if n = 13735 then ⟨(1132418597028757579039/1000000000000000000000000), (76549029920600193825603/125000000000000000000000), (7688251901285833/1000000000000000000000000)⟩ else
  if n = 13736 then ⟨(1132385079676127010777/1000000000000000000000000), (612380424282791461826103/1000000000000000000000000), (768679345384457/100000000000000000000000)⟩ else
  if n = 13737 then ⟨(1132351570503024480873/1000000000000000000000000), (306184305462681828415821/500000000000000000000000), (1537067078612343/200000000000000000000000)⟩ else
  if n = 13738 then ⟨(1132318069506836913113/1000000000000000000000000), (153089199823029001641831/250000000000000000000000), (3841938859402831/500000000000000000000000)⟩ else
  if n = 13739 then ⟨(70767786042809600371/62500000000000000000000), (489875991506117275369/800000000000000000000), (3841210215472457/500000000000000000000000)⟩ else
  if n = 13740 then ⟨(566125546017381808613/500000000000000000000000), (76541647649569197657413/125000000000000000000000), (7680963529347979/1000000000000000000000000)⟩ else
  if n = 13741 then ⟨(1132217615553657071899/1000000000000000000000000), (12246427494668706322783/20000000000000000000000), (7679507013883419/1000000000000000000000000)⟩ else
  if n = 13742 then ⟨(1132184147239025813763/1000000000000000000000000), (306154784996445083236869/500000000000000000000000), (7678050884419879/1000000000000000000000000)⟩ else
  if n = 13743 then ⟨(1132150687088262751427/1000000000000000000000000), (76537220871814595765867/125000000000000000000000), (7676595140826061/1000000000000000000000000)⟩ else
  if n = 13744 then ⟨(35378663596836267313/31250000000000000000000), (612285965677913814698683/1000000000000000000000000), (7675139782970669/1000000000000000000000000)⟩ else
  if n = 13745 then ⟨(113208379126791491131/100000000000000000000000), (38267135381417502549991/62500000000000000000000), (7673684810722543/1000000000000000000000000)⟩ else
  if n = 13746 then ⟨(113205035559312062117/100000000000000000000000), (306131184124207236954399/500000000000000000000000), (15344460447901/2000000000000000000000)⟩ else
  if n = 13747 then ⟨(56600846403588709863/50000000000000000000000), (612250572114716177628841/1000000000000000000000000), (7670776022523439/1000000000000000000000000)⟩ else
  if n = 13748 then ⟨(1131983508701273867107/1000000000000000000000000), (61223877770118433793109/100000000000000000000000), (7669322206310339/1000000000000000000000000)⟩ else
  if n = 13749 then ⟨(1131950097479018269193/1000000000000000000000000), (122445397001483656926857/200000000000000000000000), (7667868775180213/1000000000000000000000000)⟩ else
  if n = 13750 then ⟨(1131916694402407103983/1000000000000000000000000), (612215194033017533941273/1000000000000000000000000), (61331325832017/8000000000000000000000)⟩ else
  if n = 13751 then ⟨(1131883299468841133367/1000000000000000000000000), (306101702388790808303021/500000000000000000000000), (7664963067645199/1000000000000000000000000)⟩ else
  if n = 13752 then ⟨(565924956337860765221/500000000000000000000000), (76523952155088784579807/125000000000000000000000), (7663510790978587/1000000000000000000000000)⟩ else
  if n = 13753 then ⟨(113181653402045182847/100000000000000000000000), (61217983142200335706479/100000000000000000000000), (7662058898871547/1000000000000000000000000)⟩ else
  if n = 13754 then ⟨(70736447718777248141/62500000000000000000000), (24486721892842432443931/40000000000000000000000), (7660607391193369/1000000000000000000000000)⟩ else
  if n = 13755 then ⟨(7073436256956739431/6250000000000000000000), (24486250597499311111259/40000000000000000000000), (1914789066953343/250000000000000000000000)⟩ else
  if n = 13756 then ⟨(1131716446855784257471/1000000000000000000000000), (306072242135434709499493/500000000000000000000000), (1914426382150233/250000000000000000000000)⟩ else
  if n = 13757 then ⟨(1131683100725961584413/1000000000000000000000000), (122426541064164238491001/200000000000000000000000), (765625517342553/100000000000000000000000)⟩ else
  if n = 13758 then ⟨(226329952544203693363/200000000000000000000000), (61212092808693846730887/100000000000000000000000), (3827402601078339/500000000000000000000000)⟩ else
  if n = 13759 then ⟨(282904108209590710801/250000000000000000000000), (612109152568821949048957/1000000000000000000000000), (1913338903665973/250000000000000000000000)⟩ else
  if n = 13760 then ⟨(70723944442212812851/62500000000000000000000), (306048689383036154031473/500000000000000000000000), (3825953205408397/500000000000000000000000)⟩ else
  if n = 13761 then ⟨(1131549797429556301931/1000000000000000000000000), (153021401669572613045677/250000000000000000000000), (956307198810633/125000000000000000000000)⟩ else
  if n = 13762 then ⟨(1131516491898228488407/1000000000000000000000000), (153018459076269325736097/250000000000000000000000), (7649009153538409/1000000000000000000000000)⟩ else
  if n = 13763 then ⟨(1131483194478835023767/1000000000000000000000000), (38253879227877129712051/62500000000000000000000), (3823780549923309/500000000000000000000000)⟩ else
  ⟨(282862476292197120457/250000000000000000000000), (612050300700761990115653/1000000000000000000000000), (382305671463973/50000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13690 ≤ n) (hb : n ≤ 13764) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13690
  · exact row_13691
  · exact row_13692
  · exact row_13693
  · exact row_13694
  · exact row_13695
  · exact row_13696
  · exact row_13697
  · exact row_13698
  · exact row_13699
  · exact row_13700
  · exact row_13701
  · exact row_13702
  · exact row_13703
  · exact row_13704
  · exact row_13705
  · exact row_13706
  · exact row_13707
  · exact row_13708
  · exact row_13709
  · exact row_13710
  · exact row_13711
  · exact row_13712
  · exact row_13713
  · exact row_13714
  · exact row_13715
  · exact row_13716
  · exact row_13717
  · exact row_13718
  · exact row_13719
  · exact row_13720
  · exact row_13721
  · exact row_13722
  · exact row_13723
  · exact row_13724
  · exact row_13725
  · exact row_13726
  · exact row_13727
  · exact row_13728
  · exact row_13729
  · exact row_13730
  · exact row_13731
  · exact row_13732
  · exact row_13733
  · exact row_13734
  · exact row_13735
  · exact row_13736
  · exact row_13737
  · exact row_13738
  · exact row_13739
  · exact row_13740
  · exact row_13741
  · exact row_13742
  · exact row_13743
  · exact row_13744
  · exact row_13745
  · exact row_13746
  · exact row_13747
  · exact row_13748
  · exact row_13749
  · exact row_13750
  · exact row_13751
  · exact row_13752
  · exact row_13753
  · exact row_13754
  · exact row_13755
  · exact row_13756
  · exact row_13757
  · exact row_13758
  · exact row_13759
  · exact row_13760
  · exact row_13761
  · exact row_13762
  · exact row_13763
  · exact row_13764

end BstLean.Part271.R3.Rows13690
