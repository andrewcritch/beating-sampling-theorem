import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14150–14160. -/
namespace BstLean.Part271.R3.Rows14150
open Real BstLean.Part130 BstLean.Part227

theorem width_14150 : mW 14150 = 337013687353981 := by
  have hu : mW 14150 ≤ 337013687353981 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14150 ≤ 337013687353980 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14150 : RowArithmetic 14150 (1119181869529608663387/1000000000000000000000000) (607632526967832973499023/1000000000000000000000000) (1422943983036667/200000000000000000000000) where
  r0 := (594107917611/1000000000000000000)
  k0 := (728788363205831/200000000000000000)
  k6 := (5755624073944143/500000000000000000)
  q := (168226038412607220263/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14150]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14150]

theorem width_14151 : mW 14151 = 337097054994247 := by
  have hu : mW 14151 ≤ 337097054994247 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14151 ≤ 337097054994246 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14151 : RowArithmetic 14151 (1119151533870894586991/1000000000000000000000000) (607621394505584282829523/1000000000000000000000000) (355670562108651/50000000000000000000000) where
  r0 := (37127808971/62500000000000000)
  k0 := (3643748686178783/1000000000000000000)
  k6 := (11510841411561537/1000000000000000000)
  q := (6729279307622770981/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14151]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14151]

theorem width_14152 : mW 14152 = 337180437364039 := by
  have hu : mW 14152 ≤ 337180437364039 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14152 ≤ 337180437364038 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14152 : RowArithmetic 14152 (279780301347651417933/250000000000000000000000) (151902565902876926470657/250000000000000000000000) (711210290560817/100000000000000000000000) where
  r0 := (118796396117/200000000000000000)
  k0 := (1821777790104679/500000000000000000)
  k6 := (5755217359173191/500000000000000000)
  q := (42059481689626181127/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14152]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14152]

theorem width_14153 : mW 14153 = 337263834464917 := by
  have hu : mW 14153 ≤ 337263834464917 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14153 ≤ 337263834464916 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14153 : RowArithmetic 14153 (139886360510814896609/125000000000000000000000) (607599134285250292776887/1000000000000000000000000) (284431796215111/40000000000000000000000) where
  r0 := (593919028757/1000000000000000000)
  k0 := (910840624530403/250000000000000000)
  k6 := (2877507017058801/250000000000000000)
  q := (2628810478381809859/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14153]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14153]

theorem width_14154 : mW 14154 = 337347246298443 := by
  have hu : mW 14154 ≤ 337347246298443 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14154 ≤ 337347246298442 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14154 : RowArithmetic 14154 (44762422798256485081/40000000000000000000000) (303794003263229597641513/500000000000000000000000) (7109487241370827/1000000000000000000000000) where
  r0 := (593856088047/1000000000000000000)
  k0 := (910792359976001/250000000000000000)
  k6 := (11509621461220391/1000000000000000000)
  q := (84124907132192425381/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14154]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14154]

theorem width_14155 : mW 14155 = 337430672866178 := by
  have hu : mW 14155 ≤ 337430672866178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14155 ≤ 337430672866177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14155 : RowArithmetic 14155 (139878782874757875123/125000000000000000000000) (24303075213391268065721/40000000000000000000000) (1421635982695277/200000000000000000000000) where
  r0 := (593793158453/1000000000000000000)
  k0 := (1821488202777097/500000000000000000)
  k6 := (1150921489729433/100000000000000000)
  q := (168255757702374036767/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14155]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14155]

theorem width_14156 : mW 14156 = 337514114169685 := by
  have hu : mW 14156 ≤ 337514114169685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14156 ≤ 337514114169684 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14156 : RowArithmetic 14156 (223799992641850008761/200000000000000000000000) (303782877854932620335139/500000000000000000000000) (3553436460791757/500000000000000000000000) where
  r0 := (593730239973/1000000000000000000)
  k0 := (45534792438373/12500000000000000)
  k6 := (11508808376449413/1000000000000000000)
  q := (168261700930425637963/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14156]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14156]

theorem width_14157 : mW 14157 = 337597570210524 := by
  have hu : mW 14157 ≤ 337597570210524 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14157 ≤ 337597570210523 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14157 : RowArithmetic 14157 (1118969670587754031381/1000000000000000000000000) (151888658162839319599963/250000000000000000000000) (7105566265581383/1000000000000000000000000) where
  r0 := (593667332603/1000000000000000000)
  k0 := (1821295204221233/500000000000000000)
  k6 := (1150840189867803/100000000000000000)
  q := (168267643948561899391/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14157]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14157]

theorem width_14158 : mW 14158 = 337681040990257 := by
  have hu : mW 14158 ≤ 337681040990257 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14158 ≤ 337681040990256 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14158 : RowArithmetic 14158 (279734846282838880241/250000000000000000000000) (607543511158905419536521/1000000000000000000000000) (710425994535917/100000000000000000000000) where
  r0 := (593604436341/1000000000000000000)
  k0 := (3642397445669727/1000000000000000000)
  k6 := (11507995463972577/1000000000000000000)
  q := (84136793378402531083/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14158]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14158]

theorem width_14159 : mW 14159 = 337764526510447 := by
  have hu : mW 14159 ≤ 337764526510447 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14159 ≤ 337764526510446 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14159 : RowArithmetic 14159 (1118909106837835401079/1000000000000000000000000) (607532391232157367544767/1000000000000000000000000) (1775738490201519/250000000000000000000000) where
  r0 := (118708310237/200000000000000000)
  k0 := (1821102253374639/500000000000000000)
  k6 := (1438448634040681/125000000000000000)
  q := (6731181174207094539/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14159]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14159]

theorem width_14160 : mW 14160 = 337848026772653 := by
  have hu : mW 14160 ≤ 337848026772653 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14160 ≤ 337848026772652 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14160 : RowArithmetic 14160 (55943941785248881579/50000000000000000000000) (3797007955442256169939/6250000000000000000000) (7101648311811429/1000000000000000000000000) where
  r0 := (59347867713/100000000000000000)
  k0 := (56906431119837/15625000000000000)
  k6 := (11507182723729043/1000000000000000000)
  q := (168285471743701036577/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14160]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14160]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14150 then ⟨(1119181869529608663387/1000000000000000000000000), (607632526967832973499023/1000000000000000000000000), (1422943983036667/200000000000000000000000)⟩ else
  if n = 14151 then ⟨(1119151533870894586991/1000000000000000000000000), (607621394505584282829523/1000000000000000000000000), (355670562108651/50000000000000000000000)⟩ else
  if n = 14152 then ⟨(279780301347651417933/250000000000000000000000), (151902565902876926470657/250000000000000000000000), (711210290560817/100000000000000000000000)⟩ else
  if n = 14153 then ⟨(139886360510814896609/125000000000000000000000), (607599134285250292776887/1000000000000000000000000), (284431796215111/40000000000000000000000)⟩ else
  if n = 14154 then ⟨(44762422798256485081/40000000000000000000000), (303794003263229597641513/500000000000000000000000), (7109487241370827/1000000000000000000000000)⟩ else
  if n = 14155 then ⟨(139878782874757875123/125000000000000000000000), (24303075213391268065721/40000000000000000000000), (1421635982695277/200000000000000000000000)⟩ else
  if n = 14156 then ⟨(223799992641850008761/200000000000000000000000), (303782877854932620335139/500000000000000000000000), (3553436460791757/500000000000000000000000)⟩ else
  if n = 14157 then ⟨(1118969670587754031381/1000000000000000000000000), (151888658162839319599963/250000000000000000000000), (7105566265581383/1000000000000000000000000)⟩ else
  if n = 14158 then ⟨(279734846282838880241/250000000000000000000000), (607543511158905419536521/1000000000000000000000000), (710425994535917/100000000000000000000000)⟩ else
  if n = 14159 then ⟨(1118909106837835401079/1000000000000000000000000), (607532391232157367544767/1000000000000000000000000), (1775738490201519/250000000000000000000000)⟩ else
  ⟨(55943941785248881579/50000000000000000000000), (3797007955442256169939/6250000000000000000000), (7101648311811429/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14150 ≤ n) (hb : n ≤ 14160) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14150
  · exact row_14151
  · exact row_14152
  · exact row_14153
  · exact row_14154
  · exact row_14155
  · exact row_14156
  · exact row_14157
  · exact row_14158
  · exact row_14159
  · exact row_14160

end BstLean.Part271.R3.Rows14150
