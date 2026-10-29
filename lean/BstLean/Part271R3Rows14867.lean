import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14867–14883. -/
namespace BstLean.Part271.R3.Rows14867
open Real BstLean.Part130 BstLean.Part227

theorem width_14867 : mW 14867 = 400665266255430 := by
  have hu : mW 14867 ≤ 400665266255430 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14867 ≤ 400665266255429 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14867 : RowArithmetic 14867 (1099146500087719490643/1000000000000000000000000) (300016307226715526566239/500000000000000000000000) (6256426491314159/1000000000000000000000000) where
  r0 := (137912933573/250000000000000000)
  k0 := (3511326851978637/1000000000000000000)
  k6 := (5615119065295171/500000000000000000)
  q := (172435495185881030369/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14867]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14867]

theorem width_14868 : mW 14868 = 400759599096083 := by
  have hu : mW 14868 ≤ 400759599096083 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14868 ≤ 400759599096082 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14868 : RowArithmetic 14868 (8792966309871900229/8000000000000000000000) (150005630501195343689929/250000000000000000000000) (3127666534170327/500000000000000000000000) where
  r0 := (551596080291/1000000000000000000)
  k0 := (3511149725446617/1000000000000000000)
  k6 := (11229860459519273/1000000000000000000)
  q := (172441294358398968729/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14868]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14868]

theorem width_14869 : mW 14869 = 400853947799794 := by
  have hu : mW 14869 ≤ 400853947799794 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14869 ≤ 400853947799793 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14869 : RowArithmetic 14869 (1099095083161167541419/1000000000000000000000000) (60001243089680734706443/100000000000000000000000) (1563559978123499/250000000000000000000000) where
  r0 := (551540435647/1000000000000000000)
  k0 := (1755486309880431/500000000000000000)
  k6 := (11229482826548691/1000000000000000000)
  q := (43111773333974560597/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14869]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14869]

theorem width_14870 : mW 14870 = 400948312368162 := by
  have hu : mW 14870 ≤ 400948312368162 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14870 ≤ 400948312368161 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14870 : RowArithmetic 14870 (274767345841889612011/250000000000000000000000) (600002341129224340421331/1000000000000000000000000) (312657351184521/50000000000000000000000) where
  r0 := (275742400179/500000000000000000)
  k0 := (1755397767459081/500000000000000000)
  k6 := (11229105231672189/1000000000000000000)
  q := (1724528921183985247/10000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14870]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14870]

theorem width_14871 : mW 14871 = 401042692802787 := by
  have hu : mW 14871 ≤ 401042692802787 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14871 ≤ 401042692802786 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14871 : RowArithmetic 14871 (1099043689351459395657/1000000000000000000000000) (599992252701747789768491/1000000000000000000000000) (6252054401846179/1000000000000000000000000) where
  r0 := (275714587211/500000000000000000)
  k0 := (3510618470915303/1000000000000000000)
  k6 := (2807181918720841/250000000000000000)
  q := (172458690705919485709/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14871]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14871]

theorem width_14872 : mW 14872 = 401137089105271 := by
  have hu : mW 14872 ≤ 401137089105271 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14872 ≤ 401137089105270 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14872 : RowArithmetic 14872 (274754500277792337081/250000000000000000000000) (119996433122818638028031/200000000000000000000000) (6250962046877527/1000000000000000000000000) where
  r0 := (551373557837/1000000000000000000)
  k0 := (3510441427749073/1000000000000000000)
  k6 := (11228350156175813/1000000000000000000)
  q := (86232244549240396077/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14872]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14872]

theorem width_14873 : mW 14873 = 401231501277214 := by
  have hu : mW 14873 ≤ 401231501277214 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14873 ≤ 401231501277213 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14873 : RowArithmetic 14873 (549496159322494367277/500000000000000000000000) (9374563747905877635297/15625000000000000000000) (312493497935039/50000000000000000000000) where
  r0 := (2756589753/5000000000000000)
  k0 := (1755132202706537/500000000000000000)
  k6 := (5613986337771567/500000000000000000)
  q := (43117571824025526867/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14873]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14873]

theorem width_14874 : mW 14874 = 401325929320216 := by
  have hu : mW 14874 ≤ 401325929320216 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14874 ≤ 401325929320215 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14874 : RowArithmetic 14874 (549483320975609311293/500000000000000000000000) (599961995457112461293223/1000000000000000000000000) (6248778137232291/1000000000000000000000000) where
  r0 := (551262352709/1000000000000000000)
  k0 := (351008740390409/100000000000000000)
  k6 := (701724702061183/62500000000000000)
  q := (2694938832793798309/15625000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14874]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14874]

theorem width_14875 : mW 14875 = 401420373235878 := by
  have hu : mW 14875 ≤ 401420373235878 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14875 ≤ 401420373235877 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14875 : RowArithmetic 14875 (549470485514080154417/500000000000000000000000) (119990382477443552701079/200000000000000000000000) (3123843291194213/500000000000000000000000) where
  r0 := (275603382081/500000000000000000)
  k0 := (438738802902363/125000000000000000)
  k6 := (11227217828476797/1000000000000000000)
  q := (172481883106603401903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14875]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14875]

theorem width_14876 : mW 14876 = 401514833025802 := by
  have hu : mW 14876 ≤ 401514833025802 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14876 ≤ 401514833025801 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14876 : RowArithmetic 14876 (1098915305874115318387/1000000000000000000000000) (299970915328003994346081/500000000000000000000000) (6246595294085571/1000000000000000000000000) where
  r0 := (275575592479/500000000000000000)
  k0 := (1754866731678741/500000000000000000)
  k6 := (1403355057753793/125000000000000000)
  q := (172487680719522691367/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14876]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14876]

theorem width_14877 : mW 14877 = 401609308691587 := by
  have hu : mW 14877 ≤ 401609308691587 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14877 ≤ 401609308691586 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14877 : RowArithmetic 14877 (274722411621846762289/250000000000000000000000) (599931750263199036384749/1000000000000000000000000) (6245504272240191/1000000000000000000000000) where
  r0 := (137773903773/250000000000000000)
  k0 := (3509556524307053/1000000000000000000)
  k6 := (5613231566816587/500000000000000000)
  q := (34498695627516122077/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14877]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14877]

theorem width_14878 : mW 14878 = 401703800234834 := by
  have hu : mW 14878 ≤ 401703800234834 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14878 ≤ 401703800234833 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14878 : RowArithmetic 14878 (219772798573255743077/200000000000000000000000) (599921671208506926576999/1000000000000000000000000) (6244413516768753/1000000000000000000000000) where
  r0 := (110208010913/200000000000000000)
  k0 := (70187592121479/20000000000000000)
  k6 := (11226085843278893/1000000000000000000)
  q := (172499275360796805871/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14878]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14878]

theorem width_14879 : mW 14879 = 401798307657146 := by
  have hu : mW 14879 ≤ 401798307657146 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14879 ≤ 401798307657145 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14879 : RowArithmetic 14879 (68677396563068334309/62500000000000000000000) (299955796745823899782889/500000000000000000000000) (1560830756896931/250000000000000000000000) where
  r0 := (137746125843/250000000000000000)
  k0 := (3509202708645399/1000000000000000000)
  k6 := (11225708590961109/1000000000000000000)
  q := (86252536194595460719/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14879]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14879]

theorem width_14880 : mW 14880 = 401892830960121 := by
  have hu : mW 14880 ≤ 401892830960121 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14880 ≤ 401892830960120 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14880 : RowArithmetic 14880 (1098812702914136673659/1000000000000000000000000) (74987689639042223658867/125000000000000000000000) (1560558201153421/250000000000000000000000) where
  r0 := (550928961513/1000000000000000000)
  k0 := (701805166404909/200000000000000000)
  k6 := (1403166422084179/125000000000000000)
  q := (86255434611391298699/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14880]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14880]

theorem width_14881 : mW 14881 = 401987370145362 := by
  have hu : mW 14881 ≤ 401987370145362 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14881 ≤ 401987370145361 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14881 : RowArithmetic 14881 (1098787066579712998257/1000000000000000000000000) (299945721035146616292987/500000000000000000000000) (1248228569552633/200000000000000000000000) where
  r0 := (68859178623/125000000000000000)
  k0 := (1754424488100899/500000000000000000)
  k6 := (87694954690699/7812500000000000)
  q := (86258332930795735383/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14881]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14881]

theorem width_14882 : mW 14882 = 402081925214470 := by
  have hu : mW 14882 ≤ 402081925214470 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14882 ≤ 402081925214469 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14882 : RowArithmetic 14882 (549380718002064045429/500000000000000000000000) (599881368365230378746013/1000000000000000000000000) (6240053156952767/1000000000000000000000000) where
  r0 := (68852238223/125000000000000000)
  k0 := (701734428235423/200000000000000000)
  k6 := (5612288531081421/500000000000000000)
  q := (172522462305637175253/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14882]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14882]

theorem width_14883 : mW 14883 = 402176496169045 := by
  have hu : mW 14883 ≤ 402176496169045 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14883 ≤ 402176496169044 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14883 : RowArithmetic 14883 (549367905592844383553/500000000000000000000000) (599871295996865765647709/1000000000000000000000000) (3119481866049567/500000000000000000000000) where
  r0 := (55076239191/100000000000000000)
  k0 := (438561915868011/125000000000000000)
  k6 := (2244839992385431/200000000000000000)
  q := (172528258554939341277/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14883]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14883]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14867 then ⟨(1099146500087719490643/1000000000000000000000000), (300016307226715526566239/500000000000000000000000), (6256426491314159/1000000000000000000000000)⟩ else
  if n = 14868 then ⟨(8792966309871900229/8000000000000000000000), (150005630501195343689929/250000000000000000000000), (3127666534170327/500000000000000000000000)⟩ else
  if n = 14869 then ⟨(1099095083161167541419/1000000000000000000000000), (60001243089680734706443/100000000000000000000000), (1563559978123499/250000000000000000000000)⟩ else
  if n = 14870 then ⟨(274767345841889612011/250000000000000000000000), (600002341129224340421331/1000000000000000000000000), (312657351184521/50000000000000000000000)⟩ else
  if n = 14871 then ⟨(1099043689351459395657/1000000000000000000000000), (599992252701747789768491/1000000000000000000000000), (6252054401846179/1000000000000000000000000)⟩ else
  if n = 14872 then ⟨(274754500277792337081/250000000000000000000000), (119996433122818638028031/200000000000000000000000), (6250962046877527/1000000000000000000000000)⟩ else
  if n = 14873 then ⟨(549496159322494367277/500000000000000000000000), (9374563747905877635297/15625000000000000000000), (312493497935039/50000000000000000000000)⟩ else
  if n = 14874 then ⟨(549483320975609311293/500000000000000000000000), (599961995457112461293223/1000000000000000000000000), (6248778137232291/1000000000000000000000000)⟩ else
  if n = 14875 then ⟨(549470485514080154417/500000000000000000000000), (119990382477443552701079/200000000000000000000000), (3123843291194213/500000000000000000000000)⟩ else
  if n = 14876 then ⟨(1098915305874115318387/1000000000000000000000000), (299970915328003994346081/500000000000000000000000), (6246595294085571/1000000000000000000000000)⟩ else
  if n = 14877 then ⟨(274722411621846762289/250000000000000000000000), (599931750263199036384749/1000000000000000000000000), (6245504272240191/1000000000000000000000000)⟩ else
  if n = 14878 then ⟨(219772798573255743077/200000000000000000000000), (599921671208506926576999/1000000000000000000000000), (6244413516768753/1000000000000000000000000)⟩ else
  if n = 14879 then ⟨(68677396563068334309/62500000000000000000000), (299955796745823899782889/500000000000000000000000), (1560830756896931/250000000000000000000000)⟩ else
  if n = 14880 then ⟨(1098812702914136673659/1000000000000000000000000), (74987689639042223658867/125000000000000000000000), (1560558201153421/250000000000000000000000)⟩ else
  if n = 14881 then ⟨(1098787066579712998257/1000000000000000000000000), (299945721035146616292987/500000000000000000000000), (1248228569552633/200000000000000000000000)⟩ else
  if n = 14882 then ⟨(549380718002064045429/500000000000000000000000), (599881368365230378746013/1000000000000000000000000), (6240053156952767/1000000000000000000000000)⟩ else
  ⟨(549367905592844383553/500000000000000000000000), (599871295996865765647709/1000000000000000000000000), (3119481866049567/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14867 ≤ n) (hb : n ≤ 14883) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14867
  · exact row_14868
  · exact row_14869
  · exact row_14870
  · exact row_14871
  · exact row_14872
  · exact row_14873
  · exact row_14874
  · exact row_14875
  · exact row_14876
  · exact row_14877
  · exact row_14878
  · exact row_14879
  · exact row_14880
  · exact row_14881
  · exact row_14882
  · exact row_14883

end BstLean.Part271.R3.Rows14867
